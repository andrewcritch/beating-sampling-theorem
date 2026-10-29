import BstLean.Part262ActualShard0Step0


/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12225 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12225).real (BstLean.Part211.CentreSource 12225 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12225) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12225 160 (6 / 1000)
  have hj := jS_160_le (n := 12225) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12225 160 (6 / 1000) ^ 2 * 12225 /
      (((12225 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12225 160 (6 / 1000) ^ 2 * 12225 /
      (((12225 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12225 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12225 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12225) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12225 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12225

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12225) :=
  Ethm (paperCentres 12225) ∩ Ethp (paperCentres 12225)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12225)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12225)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12225) (paperCentres 12225)
  have he : exp (-(45 / 10000 * (12225 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12225 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12225) :=
  (passEvent ∩ agentEv (paperDesignP 12225) (DirectionError 12225) ∩
    agentEv (paperDesignP 12225) (CentreSources 12225 12225)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12225)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12225) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12225) hτ
  have hC := centreSources_ret_charge_row 12225 (paperDesignP 12225) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12225)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12225) (CentreSources 12225 12225)
  direction : analyticBase ⊆ agentEv (paperDesignP 12225) (DirectionError 12225)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12225)) : Set (Ret 12225) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12225)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12225)}
    (hT : (retDist (paperCentres 12225)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12225)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12225)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12225)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12225)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12225)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12225

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12225 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12225 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12225 12225 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12225)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12225)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12225
  have hb0 := BstLean.Part150.betaJ_nonneg 12225
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12225 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12225 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12225 * BstLean.Part150.betaJ 12225) * 12225) ≤
      (157223693 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12225)) * 12225 := by gcongr <;> linarith
      _ ≤ ((157223693 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12225 * 12225 *
      (1 + BstLean.Part154.deltaChi 12225 12 + 2 / π) / BstLean.Part154.csC) ≤
      (89980777 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12225 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((89980777 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12225 : ℝ) / BstLean.Part154.csC) ≤ (97152581 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12225 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97152581 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12225 : ℝ) * (157223693 / 1000000) +
        2 * (1792 / 10000 / 12225) * (89980777 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (97152581 / 1000000) *
          (81 / 1000 / 12225 + (1792 / 10000 / 12225) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12225

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12225
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12225 ∧
    1 ≤ gPlus 12225 ∧ gPlus 12225 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12225 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12225 : ℝ) < √(1 - 2 / (12225 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12225 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12225 (gMinus 12225) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12225 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12225 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12225 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12225)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12225 (gMinus 12225) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12225 (gMinus 12225) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12225 (gMinus 12225) (54 / 100))
    (by linarith : energyRatio 12225 (gMinus 12225) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12225 (gMinus 12225) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12225 * kappa (energyRatio 12225 (gMinus 12225) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12225) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12225 12225 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12225 12225 (11 / 1000) / √12225 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12225)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12225 * kappa (energyRatio 12225 (gMinus 12225) (54 / 100))) +
      2 * √(12 * gPlus 12225) / 12225 + finiteEnergy 12225 12225 (11 / 1000) / √12225 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12225 θ ∧ meanLowerRoot 12225 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12225 - 2 / (12225 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12225 - 2 / (12225 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12225 θ ^ 2 / gPlus 12225) - 2 / (12225 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12225 * (kappa (meanLowerRoot 12225 θ ^ 2 / gPlus 12225) -
        2 / (12225 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12225) / 12225 -
        finiteEnergy 12225 12225 (11 / 1000) / √12225 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12225 θ ^ 2 / gPlus 12225 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12225)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12225 θ ^ 2 / gPlus 12225 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12225)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12225 θ ^ 2 / gPlus 12225 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12225 ^ 2 ≤
      kappa (meanLowerRoot 12225 θ ^ 2 / gPlus 12225) - 2 / (12225 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12225 *
      (kappa (meanLowerRoot 12225 θ ^ 2 / gPlus 12225) - 2 / (12225 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12225 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12225)
    linarith
  have ht : √(12 * gPlus 12225) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12225 12225 (11 / 1000) / √12225 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12225)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12225) (hτ : 0 < (paperDesignP 12225).tau0 c) :
    eR c = (2 / (mA 12225 : ℝ)) *
      normSq (BstLean.Part150.bT 12225 12225 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12225).tau0 c)) /
      (2 / (12225 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12225).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12225).tau0 c))⁻¹ •
      BstLean.Part150.bT 12225 12225 (A1 c) (A2 c) c.1.2 ((paperDesignP 12225).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12225 : ℝ)) * normSq (bR c) / (2 / (12225 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12225}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12225) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12225 : ℝ) * (paperDesignP 12225).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12225 12225 c.1.2 ((paperDesignP 12225).tau0 c) :=
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

end BstLean.Part262.Row12225

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12227 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12227).real (BstLean.Part211.CentreSource 12227 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12227) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12227 160 (6 / 1000)
  have hj := jS_160_le (n := 12227) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12227 160 (6 / 1000) ^ 2 * 12227 /
      (((12227 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12227 160 (6 / 1000) ^ 2 * 12227 /
      (((12227 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12227 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12227 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12227) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12227 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12227

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12227) :=
  Ethm (paperCentres 12227) ∩ Ethp (paperCentres 12227)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12227)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12227)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12227) (paperCentres 12227)
  have he : exp (-(45 / 10000 * (12227 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12227 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12227) :=
  (passEvent ∩ agentEv (paperDesignP 12227) (DirectionError 12227) ∩
    agentEv (paperDesignP 12227) (CentreSources 12227 12227)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12227)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12227) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12227) hτ
  have hC := centreSources_ret_charge_row 12227 (paperDesignP 12227) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12227)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12227) (CentreSources 12227 12227)
  direction : analyticBase ⊆ agentEv (paperDesignP 12227) (DirectionError 12227)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12227)) : Set (Ret 12227) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12227)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12227)}
    (hT : (retDist (paperCentres 12227)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12227)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12227)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12227)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12227)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12227)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12227

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12227 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12227 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12227 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12227 12227 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12227)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12227)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12227
  have hb0 := BstLean.Part150.betaJ_nonneg 12227
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12227 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12227 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12227 * BstLean.Part150.betaJ 12227) * 12227) ≤
      (157236553 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12227)) * 12227 := by gcongr <;> linarith
      _ ≤ ((157236553 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12227 * 12227 *
      (1 + BstLean.Part154.deltaChi 12227 12 + 2 / π) / BstLean.Part154.csC) ≤
      (89988137 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12227 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((89988137 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12227 : ℝ) / BstLean.Part154.csC) ≤ (97160527 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12227 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97160527 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12227 : ℝ) * (157236553 / 1000000) +
        2 * (1792 / 10000 / 12227) * (89988137 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (97160527 / 1000000) *
          (81 / 1000 / 12227 + (1792 / 10000 / 12227) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12227

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12227
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12227 ∧
    1 ≤ gPlus 12227 ∧ gPlus 12227 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12227 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12227 : ℝ) < √(1 - 2 / (12227 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12227 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12227 (gMinus 12227) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12227 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12227 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12227 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12227)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12227 (gMinus 12227) (gPlus 12227)
      (finiteEnergy 12227 12227 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12227 (gMinus 12227) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12227 (gMinus 12227) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12227 (gMinus 12227) (54 / 100))
    (by linarith : energyRatio 12227 (gMinus 12227) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12227 (gMinus 12227) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12227 * kappa (energyRatio 12227 (gMinus 12227) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12227) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12227 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12227 12227 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12227 12227 (11 / 1000) / √12227 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12227)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12227 * kappa (energyRatio 12227 (gMinus 12227) (54 / 100))) +
      2 * √(12 * gPlus 12227) / 12227 + finiteEnergy 12227 12227 (11 / 1000) / √12227 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12227 θ ∧ meanLowerRoot 12227 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12227 - 2 / (12227 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12227 - 2 / (12227 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12227 θ ^ 2 / gPlus 12227) - 2 / (12227 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12227 * (kappa (meanLowerRoot 12227 θ ^ 2 / gPlus 12227) -
        2 / (12227 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12227) / 12227 -
        finiteEnergy 12227 12227 (11 / 1000) / √12227 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12227 θ ^ 2 / gPlus 12227 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12227)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12227 θ ^ 2 / gPlus 12227 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12227)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12227 θ ^ 2 / gPlus 12227 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12227 ^ 2 ≤
      kappa (meanLowerRoot 12227 θ ^ 2 / gPlus 12227) - 2 / (12227 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12227 *
      (kappa (meanLowerRoot 12227 θ ^ 2 / gPlus 12227) - 2 / (12227 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12227 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12227)
    linarith
  have ht : √(12 * gPlus 12227) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12227 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12227 12227 (11 / 1000) / √12227 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12227)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12227 (gMinus 12227) (gPlus 12227)
      (finiteEnergy 12227 12227 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12227) (hτ : 0 < (paperDesignP 12227).tau0 c) :
    eR c = (2 / (mA 12227 : ℝ)) *
      normSq (BstLean.Part150.bT 12227 12227 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12227).tau0 c)) /
      (2 / (12227 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12227).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12227).tau0 c))⁻¹ •
      BstLean.Part150.bT 12227 12227 (A1 c) (A2 c) c.1.2 ((paperDesignP 12227).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12227 : ℝ)) * normSq (bR c) / (2 / (12227 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12227}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12227) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12227).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12227 : ℝ) * (paperDesignP 12227).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12227 12227 c.1.2 ((paperDesignP 12227).tau0 c) :=
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

end BstLean.Part262.Row12227

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12228 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12228).real (BstLean.Part211.CentreSource 12228 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12228) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12228 160 (6 / 1000)
  have hj := jS_160_le (n := 12228) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12228 160 (6 / 1000) ^ 2 * 12228 /
      (((12228 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12228 160 (6 / 1000) ^ 2 * 12228 /
      (((12228 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12228 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12228 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12228) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12228 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12228

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12228) :=
  Ethm (paperCentres 12228) ∩ Ethp (paperCentres 12228)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12228)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12228)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12228) (paperCentres 12228)
  have he : exp (-(45 / 10000 * (12228 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12228 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12228) :=
  (passEvent ∩ agentEv (paperDesignP 12228) (DirectionError 12228) ∩
    agentEv (paperDesignP 12228) (CentreSources 12228 12228)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12228)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12228) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12228) hτ
  have hC := centreSources_ret_charge_row 12228 (paperDesignP 12228) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12228)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12228) (CentreSources 12228 12228)
  direction : analyticBase ⊆ agentEv (paperDesignP 12228) (DirectionError 12228)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12228)) : Set (Ret 12228) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12228)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12228)}
    (hT : (retDist (paperCentres 12228)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12228)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12228)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12228)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12228)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12228)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12228

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12228 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12228 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12228 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12228 12228 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12228)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12228)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12228
  have hb0 := BstLean.Part150.betaJ_nonneg 12228
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12228 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12228 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12228 * BstLean.Part150.betaJ 12228) * 12228) ≤
      (157242983 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12228)) * 12228 := by gcongr <;> linarith
      _ ≤ ((157242983 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12228 * 12228 *
      (1 + BstLean.Part154.deltaChi 12228 12 + 2 / π) / BstLean.Part154.csC) ≤
      (89991817 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12228 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((89991817 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12228 : ℝ) / BstLean.Part154.csC) ≤ (97164501 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12228 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97164501 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12228 : ℝ) * (157242983 / 1000000) +
        2 * (1792 / 10000 / 12228) * (89991817 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (97164501 / 1000000) *
          (81 / 1000 / 12228 + (1792 / 10000 / 12228) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12228

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12228
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12228 ∧
    1 ≤ gPlus 12228 ∧ gPlus 12228 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12228 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12228 : ℝ) < √(1 - 2 / (12228 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12228 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12228 (gMinus 12228) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12228 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12228 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12228 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12228)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12228 (gMinus 12228) (gPlus 12228)
      (finiteEnergy 12228 12228 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12228 (gMinus 12228) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12228 (gMinus 12228) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12228 (gMinus 12228) (54 / 100))
    (by linarith : energyRatio 12228 (gMinus 12228) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12228 (gMinus 12228) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12228 * kappa (energyRatio 12228 (gMinus 12228) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12228) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12228 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12228 12228 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12228 12228 (11 / 1000) / √12228 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12228)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12228 * kappa (energyRatio 12228 (gMinus 12228) (54 / 100))) +
      2 * √(12 * gPlus 12228) / 12228 + finiteEnergy 12228 12228 (11 / 1000) / √12228 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12228 θ ∧ meanLowerRoot 12228 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12228 - 2 / (12228 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12228 - 2 / (12228 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12228 θ ^ 2 / gPlus 12228) - 2 / (12228 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12228 * (kappa (meanLowerRoot 12228 θ ^ 2 / gPlus 12228) -
        2 / (12228 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12228) / 12228 -
        finiteEnergy 12228 12228 (11 / 1000) / √12228 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12228 θ ^ 2 / gPlus 12228 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12228)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12228 θ ^ 2 / gPlus 12228 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12228)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12228 θ ^ 2 / gPlus 12228 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12228 ^ 2 ≤
      kappa (meanLowerRoot 12228 θ ^ 2 / gPlus 12228) - 2 / (12228 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12228 *
      (kappa (meanLowerRoot 12228 θ ^ 2 / gPlus 12228) - 2 / (12228 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12228 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12228)
    linarith
  have ht : √(12 * gPlus 12228) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12228 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12228 12228 (11 / 1000) / √12228 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12228)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12228 (gMinus 12228) (gPlus 12228)
      (finiteEnergy 12228 12228 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12228) (hτ : 0 < (paperDesignP 12228).tau0 c) :
    eR c = (2 / (mA 12228 : ℝ)) *
      normSq (BstLean.Part150.bT 12228 12228 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12228).tau0 c)) /
      (2 / (12228 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12228).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12228).tau0 c))⁻¹ •
      BstLean.Part150.bT 12228 12228 (A1 c) (A2 c) c.1.2 ((paperDesignP 12228).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12228 : ℝ)) * normSq (bR c) / (2 / (12228 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12228}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12228) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12228).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12228 : ℝ) * (paperDesignP 12228).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12228 12228 c.1.2 ((paperDesignP 12228).tau0 c) :=
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

end BstLean.Part262.Row12228

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12229 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12229).real (BstLean.Part211.CentreSource 12229 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12229) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12229 160 (6 / 1000)
  have hj := jS_160_le (n := 12229) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12229 160 (6 / 1000) ^ 2 * 12229 /
      (((12229 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12229 160 (6 / 1000) ^ 2 * 12229 /
      (((12229 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12229 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12229 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12229) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12229 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12229

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12229) :=
  Ethm (paperCentres 12229) ∩ Ethp (paperCentres 12229)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12229)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12229)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12229) (paperCentres 12229)
  have he : exp (-(45 / 10000 * (12229 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12229 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12229) :=
  (passEvent ∩ agentEv (paperDesignP 12229) (DirectionError 12229) ∩
    agentEv (paperDesignP 12229) (CentreSources 12229 12229)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12229)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12229) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12229) hτ
  have hC := centreSources_ret_charge_row 12229 (paperDesignP 12229) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12229)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12229) (CentreSources 12229 12229)
  direction : analyticBase ⊆ agentEv (paperDesignP 12229) (DirectionError 12229)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12229)) : Set (Ret 12229) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12229)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12229)}
    (hT : (retDist (paperCentres 12229)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12229)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12229)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12229)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12229)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12229)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12229

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12229 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12229 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12229 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12229 12229 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12229)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12229)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12229
  have hb0 := BstLean.Part150.betaJ_nonneg 12229
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12229 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12229 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12229 * BstLean.Part150.betaJ 12229) * 12229) ≤
      (39312353 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12229)) * 12229 := by gcongr <;> linarith
      _ ≤ ((39312353 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12229 * 12229 *
      (1 + BstLean.Part154.deltaChi 12229 12 + 2 / π) / BstLean.Part154.csC) ≤
      (179990993 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12229 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((179990993 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12229 : ℝ) / BstLean.Part154.csC) ≤ (48584237 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12229 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48584237 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12229 : ℝ) * (39312353 / 250000) +
        2 * (1792 / 10000 / 12229) * (179990993 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (48584237 / 500000) *
          (81 / 1000 / 12229 + (1792 / 10000 / 12229) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12229

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12229
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12229 ∧
    1 ≤ gPlus 12229 ∧ gPlus 12229 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12229 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12229 : ℝ) < √(1 - 2 / (12229 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12229 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12229 (gMinus 12229) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12229 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12229 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12229 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12229)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12229 (gMinus 12229) (gPlus 12229)
      (finiteEnergy 12229 12229 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12229 (gMinus 12229) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12229 (gMinus 12229) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12229 (gMinus 12229) (54 / 100))
    (by linarith : energyRatio 12229 (gMinus 12229) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12229 (gMinus 12229) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12229 * kappa (energyRatio 12229 (gMinus 12229) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12229) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12229 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12229 12229 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12229 12229 (11 / 1000) / √12229 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12229)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12229 * kappa (energyRatio 12229 (gMinus 12229) (54 / 100))) +
      2 * √(12 * gPlus 12229) / 12229 + finiteEnergy 12229 12229 (11 / 1000) / √12229 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12229 θ ∧ meanLowerRoot 12229 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12229 - 2 / (12229 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12229 - 2 / (12229 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12229 θ ^ 2 / gPlus 12229) - 2 / (12229 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12229 * (kappa (meanLowerRoot 12229 θ ^ 2 / gPlus 12229) -
        2 / (12229 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12229) / 12229 -
        finiteEnergy 12229 12229 (11 / 1000) / √12229 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12229 θ ^ 2 / gPlus 12229 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12229)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12229 θ ^ 2 / gPlus 12229 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12229)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12229 θ ^ 2 / gPlus 12229 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12229 ^ 2 ≤
      kappa (meanLowerRoot 12229 θ ^ 2 / gPlus 12229) - 2 / (12229 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12229 *
      (kappa (meanLowerRoot 12229 θ ^ 2 / gPlus 12229) - 2 / (12229 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12229 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12229)
    linarith
  have ht : √(12 * gPlus 12229) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12229 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12229 12229 (11 / 1000) / √12229 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12229)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12229 (gMinus 12229) (gPlus 12229)
      (finiteEnergy 12229 12229 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12229) (hτ : 0 < (paperDesignP 12229).tau0 c) :
    eR c = (2 / (mA 12229 : ℝ)) *
      normSq (BstLean.Part150.bT 12229 12229 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12229).tau0 c)) /
      (2 / (12229 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12229).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12229).tau0 c))⁻¹ •
      BstLean.Part150.bT 12229 12229 (A1 c) (A2 c) c.1.2 ((paperDesignP 12229).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12229 : ℝ)) * normSq (bR c) / (2 / (12229 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12229}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12229) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12229).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12229 : ℝ) * (paperDesignP 12229).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12229 12229 c.1.2 ((paperDesignP 12229).tau0 c) :=
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

end BstLean.Part262.Row12229

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12230 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12230).real (BstLean.Part211.CentreSource 12230 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12230) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12230 160 (6 / 1000)
  have hj := jS_160_le (n := 12230) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12230 160 (6 / 1000) ^ 2 * 12230 /
      (((12230 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12230 160 (6 / 1000) ^ 2 * 12230 /
      (((12230 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12230 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12230 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12230) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12230 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12230

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12230) :=
  Ethm (paperCentres 12230) ∩ Ethp (paperCentres 12230)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12230)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12230)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12230) (paperCentres 12230)
  have he : exp (-(45 / 10000 * (12230 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12230 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12230) :=
  (passEvent ∩ agentEv (paperDesignP 12230) (DirectionError 12230) ∩
    agentEv (paperDesignP 12230) (CentreSources 12230 12230)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12230)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12230) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12230) hτ
  have hC := centreSources_ret_charge_row 12230 (paperDesignP 12230) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12230)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12230) (CentreSources 12230 12230)
  direction : analyticBase ⊆ agentEv (paperDesignP 12230) (DirectionError 12230)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12230)) : Set (Ret 12230) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12230)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12230)}
    (hT : (retDist (paperCentres 12230)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12230)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12230)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12230)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12230)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12230)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12230

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12230 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12230 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12230 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12230 12230 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12230)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12230)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12230
  have hb0 := BstLean.Part150.betaJ_nonneg 12230
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12230 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12230 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12230 * BstLean.Part150.betaJ 12230) * 12230) ≤
      (157255841 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12230)) * 12230 := by gcongr <;> linarith
      _ ≤ ((157255841 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12230 * 12230 *
      (1 + BstLean.Part154.deltaChi 12230 12 + 2 / π) / BstLean.Part154.csC) ≤
      (11249897 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12230 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((11249897 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12230 : ℝ) / BstLean.Part154.csC) ≤ (48586223 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12230 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48586223 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12230 : ℝ) * (157255841 / 1000000) +
        2 * (1792 / 10000 / 12230) * (11249897 / 62500) +
        4 * (1 / 2.506628) * 1.036505 * (48586223 / 500000) *
          (81 / 1000 / 12230 + (1792 / 10000 / 12230) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12230

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12230
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12230 ∧
    1 ≤ gPlus 12230 ∧ gPlus 12230 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12230 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12230 : ℝ) < √(1 - 2 / (12230 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12230 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12230 (gMinus 12230) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12230 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12230 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12230 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12230)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12230 (gMinus 12230) (gPlus 12230)
      (finiteEnergy 12230 12230 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12230 (gMinus 12230) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12230 (gMinus 12230) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12230 (gMinus 12230) (54 / 100))
    (by linarith : energyRatio 12230 (gMinus 12230) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12230 (gMinus 12230) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12230 * kappa (energyRatio 12230 (gMinus 12230) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12230) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12230 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12230 12230 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12230 12230 (11 / 1000) / √12230 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12230)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12230 * kappa (energyRatio 12230 (gMinus 12230) (54 / 100))) +
      2 * √(12 * gPlus 12230) / 12230 + finiteEnergy 12230 12230 (11 / 1000) / √12230 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12230 θ ∧ meanLowerRoot 12230 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12230 - 2 / (12230 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12230 - 2 / (12230 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12230 θ ^ 2 / gPlus 12230) - 2 / (12230 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12230 * (kappa (meanLowerRoot 12230 θ ^ 2 / gPlus 12230) -
        2 / (12230 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12230) / 12230 -
        finiteEnergy 12230 12230 (11 / 1000) / √12230 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12230 θ ^ 2 / gPlus 12230 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12230)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12230 θ ^ 2 / gPlus 12230 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12230)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12230 θ ^ 2 / gPlus 12230 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12230 ^ 2 ≤
      kappa (meanLowerRoot 12230 θ ^ 2 / gPlus 12230) - 2 / (12230 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12230 *
      (kappa (meanLowerRoot 12230 θ ^ 2 / gPlus 12230) - 2 / (12230 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12230 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12230)
    linarith
  have ht : √(12 * gPlus 12230) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12230 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12230 12230 (11 / 1000) / √12230 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12230)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12230 (gMinus 12230) (gPlus 12230)
      (finiteEnergy 12230 12230 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12230) (hτ : 0 < (paperDesignP 12230).tau0 c) :
    eR c = (2 / (mA 12230 : ℝ)) *
      normSq (BstLean.Part150.bT 12230 12230 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12230).tau0 c)) /
      (2 / (12230 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12230).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12230).tau0 c))⁻¹ •
      BstLean.Part150.bT 12230 12230 (A1 c) (A2 c) c.1.2 ((paperDesignP 12230).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12230 : ℝ)) * normSq (bR c) / (2 / (12230 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12230}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12230) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12230).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12230 : ℝ) * (paperDesignP 12230).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12230 12230 c.1.2 ((paperDesignP 12230).tau0 c) :=
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

end BstLean.Part262.Row12230

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12231 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12231).real (BstLean.Part211.CentreSource 12231 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12231) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12231 160 (6 / 1000)
  have hj := jS_160_le (n := 12231) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12231 160 (6 / 1000) ^ 2 * 12231 /
      (((12231 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12231 160 (6 / 1000) ^ 2 * 12231 /
      (((12231 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12231 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12231 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12231) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12231 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12231

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12231) :=
  Ethm (paperCentres 12231) ∩ Ethp (paperCentres 12231)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12231)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12231)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12231) (paperCentres 12231)
  have he : exp (-(45 / 10000 * (12231 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12231 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12231) :=
  (passEvent ∩ agentEv (paperDesignP 12231) (DirectionError 12231) ∩
    agentEv (paperDesignP 12231) (CentreSources 12231 12231)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12231)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12231) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12231) hτ
  have hC := centreSources_ret_charge_row 12231 (paperDesignP 12231) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12231)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12231) (CentreSources 12231 12231)
  direction : analyticBase ⊆ agentEv (paperDesignP 12231) (DirectionError 12231)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12231)) : Set (Ret 12231) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12231)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12231)}
    (hT : (retDist (paperCentres 12231)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12231)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12231)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12231)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12231)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12231)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12231

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12231 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12231 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12231 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12231 12231 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12231)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12231)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12231
  have hb0 := BstLean.Part150.betaJ_nonneg 12231
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12231 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12231 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12231 * BstLean.Part150.betaJ 12231) * 12231) ≤
      (15726227 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12231)) * 12231 := by gcongr <;> linarith
      _ ≤ ((15726227 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12231 * 12231 *
      (1 + BstLean.Part154.deltaChi 12231 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180005711 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12231 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180005711 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12231 : ℝ) / BstLean.Part154.csC) ≤ (97176419 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12231 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97176419 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12231 : ℝ) * (15726227 / 100000) +
        2 * (1792 / 10000 / 12231) * (180005711 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97176419 / 1000000) *
          (81 / 1000 / 12231 + (1792 / 10000 / 12231) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12231

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12231
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12231 ∧
    1 ≤ gPlus 12231 ∧ gPlus 12231 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12231 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12231 : ℝ) < √(1 - 2 / (12231 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12231 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12231 (gMinus 12231) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12231 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12231 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12231 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12231)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12231 (gMinus 12231) (gPlus 12231)
      (finiteEnergy 12231 12231 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12231 (gMinus 12231) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12231 (gMinus 12231) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12231 (gMinus 12231) (54 / 100))
    (by linarith : energyRatio 12231 (gMinus 12231) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12231 (gMinus 12231) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12231 * kappa (energyRatio 12231 (gMinus 12231) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12231) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12231 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12231 12231 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12231 12231 (11 / 1000) / √12231 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12231)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12231 * kappa (energyRatio 12231 (gMinus 12231) (54 / 100))) +
      2 * √(12 * gPlus 12231) / 12231 + finiteEnergy 12231 12231 (11 / 1000) / √12231 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12231 θ ∧ meanLowerRoot 12231 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12231 - 2 / (12231 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12231 - 2 / (12231 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12231 θ ^ 2 / gPlus 12231) - 2 / (12231 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12231 * (kappa (meanLowerRoot 12231 θ ^ 2 / gPlus 12231) -
        2 / (12231 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12231) / 12231 -
        finiteEnergy 12231 12231 (11 / 1000) / √12231 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12231 θ ^ 2 / gPlus 12231 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12231)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12231 θ ^ 2 / gPlus 12231 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12231)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12231 θ ^ 2 / gPlus 12231 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12231 ^ 2 ≤
      kappa (meanLowerRoot 12231 θ ^ 2 / gPlus 12231) - 2 / (12231 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12231 *
      (kappa (meanLowerRoot 12231 θ ^ 2 / gPlus 12231) - 2 / (12231 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12231 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12231)
    linarith
  have ht : √(12 * gPlus 12231) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12231 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12231 12231 (11 / 1000) / √12231 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12231)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12231 (gMinus 12231) (gPlus 12231)
      (finiteEnergy 12231 12231 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12231) (hτ : 0 < (paperDesignP 12231).tau0 c) :
    eR c = (2 / (mA 12231 : ℝ)) *
      normSq (BstLean.Part150.bT 12231 12231 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12231).tau0 c)) /
      (2 / (12231 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12231).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12231).tau0 c))⁻¹ •
      BstLean.Part150.bT 12231 12231 (A1 c) (A2 c) c.1.2 ((paperDesignP 12231).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12231 : ℝ)) * normSq (bR c) / (2 / (12231 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12231}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12231) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12231).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12231 : ℝ) * (paperDesignP 12231).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12231 12231 c.1.2 ((paperDesignP 12231).tau0 c) :=
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

end BstLean.Part262.Row12231

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12232 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12232).real (BstLean.Part211.CentreSource 12232 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12232) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12232 160 (6 / 1000)
  have hj := jS_160_le (n := 12232) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12232 160 (6 / 1000) ^ 2 * 12232 /
      (((12232 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12232 160 (6 / 1000) ^ 2 * 12232 /
      (((12232 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12232 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12232 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12232) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12232 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12232

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12232) :=
  Ethm (paperCentres 12232) ∩ Ethp (paperCentres 12232)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12232)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12232)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12232) (paperCentres 12232)
  have he : exp (-(45 / 10000 * (12232 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12232 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12232) :=
  (passEvent ∩ agentEv (paperDesignP 12232) (DirectionError 12232) ∩
    agentEv (paperDesignP 12232) (CentreSources 12232 12232)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12232)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12232) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12232) hτ
  have hC := centreSources_ret_charge_row 12232 (paperDesignP 12232) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12232)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12232) (CentreSources 12232 12232)
  direction : analyticBase ⊆ agentEv (paperDesignP 12232) (DirectionError 12232)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12232)) : Set (Ret 12232) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12232)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12232)}
    (hT : (retDist (paperCentres 12232)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12232)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12232)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12232)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12232)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12232)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12232

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12232 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12232 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12232 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12232 12232 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12232)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12232)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12232
  have hb0 := BstLean.Part150.betaJ_nonneg 12232
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12232 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12232 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12232 * BstLean.Part150.betaJ 12232) * 12232) ≤
      (157268699 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12232)) * 12232 := by gcongr <;> linarith
      _ ≤ ((157268699 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12232 * 12232 *
      (1 + BstLean.Part154.deltaChi 12232 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180013069 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12232 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180013069 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12232 : ℝ) / BstLean.Part154.csC) ≤ (97180391 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12232 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97180391 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12232 : ℝ) * (157268699 / 1000000) +
        2 * (1792 / 10000 / 12232) * (180013069 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97180391 / 1000000) *
          (81 / 1000 / 12232 + (1792 / 10000 / 12232) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12232

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12232
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12232 ∧
    1 ≤ gPlus 12232 ∧ gPlus 12232 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12232 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12232 : ℝ) < √(1 - 2 / (12232 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12232 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12232 (gMinus 12232) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12232 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12232 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12232 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12232)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12232 (gMinus 12232) (gPlus 12232)
      (finiteEnergy 12232 12232 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12232 (gMinus 12232) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12232 (gMinus 12232) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12232 (gMinus 12232) (54 / 100))
    (by linarith : energyRatio 12232 (gMinus 12232) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12232 (gMinus 12232) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12232 * kappa (energyRatio 12232 (gMinus 12232) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12232) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12232 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12232 12232 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12232 12232 (11 / 1000) / √12232 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12232)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12232 * kappa (energyRatio 12232 (gMinus 12232) (54 / 100))) +
      2 * √(12 * gPlus 12232) / 12232 + finiteEnergy 12232 12232 (11 / 1000) / √12232 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12232 θ ∧ meanLowerRoot 12232 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12232 - 2 / (12232 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12232 - 2 / (12232 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12232 θ ^ 2 / gPlus 12232) - 2 / (12232 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12232 * (kappa (meanLowerRoot 12232 θ ^ 2 / gPlus 12232) -
        2 / (12232 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12232) / 12232 -
        finiteEnergy 12232 12232 (11 / 1000) / √12232 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12232 θ ^ 2 / gPlus 12232 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12232)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12232 θ ^ 2 / gPlus 12232 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12232)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12232 θ ^ 2 / gPlus 12232 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12232 ^ 2 ≤
      kappa (meanLowerRoot 12232 θ ^ 2 / gPlus 12232) - 2 / (12232 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12232 *
      (kappa (meanLowerRoot 12232 θ ^ 2 / gPlus 12232) - 2 / (12232 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12232 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12232)
    linarith
  have ht : √(12 * gPlus 12232) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12232 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12232 12232 (11 / 1000) / √12232 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12232)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12232 (gMinus 12232) (gPlus 12232)
      (finiteEnergy 12232 12232 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12232) (hτ : 0 < (paperDesignP 12232).tau0 c) :
    eR c = (2 / (mA 12232 : ℝ)) *
      normSq (BstLean.Part150.bT 12232 12232 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12232).tau0 c)) /
      (2 / (12232 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12232).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12232).tau0 c))⁻¹ •
      BstLean.Part150.bT 12232 12232 (A1 c) (A2 c) c.1.2 ((paperDesignP 12232).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12232 : ℝ)) * normSq (bR c) / (2 / (12232 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12232}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12232) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12232).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12232 : ℝ) * (paperDesignP 12232).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12232 12232 c.1.2 ((paperDesignP 12232).tau0 c) :=
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

end BstLean.Part262.Row12232

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12233 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12233).real (BstLean.Part211.CentreSource 12233 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12233) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12233 160 (6 / 1000)
  have hj := jS_160_le (n := 12233) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12233 160 (6 / 1000) ^ 2 * 12233 /
      (((12233 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12233 160 (6 / 1000) ^ 2 * 12233 /
      (((12233 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12233 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12233 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12233) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12233 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12233

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12233) :=
  Ethm (paperCentres 12233) ∩ Ethp (paperCentres 12233)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12233)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12233)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12233) (paperCentres 12233)
  have he : exp (-(45 / 10000 * (12233 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12233 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12233) :=
  (passEvent ∩ agentEv (paperDesignP 12233) (DirectionError 12233) ∩
    agentEv (paperDesignP 12233) (CentreSources 12233 12233)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12233)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12233) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12233) hτ
  have hC := centreSources_ret_charge_row 12233 (paperDesignP 12233) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12233)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12233) (CentreSources 12233 12233)
  direction : analyticBase ⊆ agentEv (paperDesignP 12233) (DirectionError 12233)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12233)) : Set (Ret 12233) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12233)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12233)}
    (hT : (retDist (paperCentres 12233)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12233)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12233)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12233)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12233)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12233)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12233

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12233 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12233 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12233 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12233 12233 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12233)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12233)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12233
  have hb0 := BstLean.Part150.betaJ_nonneg 12233
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12233 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12233 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12233 * BstLean.Part150.betaJ 12233) * 12233) ≤
      (157275127 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12233)) * 12233 := by gcongr <;> linarith
      _ ≤ ((157275127 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12233 * 12233 *
      (1 + BstLean.Part154.deltaChi 12233 12 + 2 / π) / BstLean.Part154.csC) ≤
      (45005107 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12233 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((45005107 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12233 : ℝ) / BstLean.Part154.csC) ≤ (24296091 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12233 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((24296091 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12233 : ℝ) * (157275127 / 1000000) +
        2 * (1792 / 10000 / 12233) * (45005107 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (24296091 / 250000) *
          (81 / 1000 / 12233 + (1792 / 10000 / 12233) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12233

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12233
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12233 ∧
    1 ≤ gPlus 12233 ∧ gPlus 12233 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12233 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12233 : ℝ) < √(1 - 2 / (12233 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12233 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12233 (gMinus 12233) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12233 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12233 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12233 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12233)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12233 (gMinus 12233) (gPlus 12233)
      (finiteEnergy 12233 12233 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12233 (gMinus 12233) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12233 (gMinus 12233) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12233 (gMinus 12233) (54 / 100))
    (by linarith : energyRatio 12233 (gMinus 12233) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12233 (gMinus 12233) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12233 * kappa (energyRatio 12233 (gMinus 12233) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12233) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12233 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12233 12233 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12233 12233 (11 / 1000) / √12233 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12233)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12233 * kappa (energyRatio 12233 (gMinus 12233) (54 / 100))) +
      2 * √(12 * gPlus 12233) / 12233 + finiteEnergy 12233 12233 (11 / 1000) / √12233 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12233 θ ∧ meanLowerRoot 12233 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12233 - 2 / (12233 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12233 - 2 / (12233 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12233 θ ^ 2 / gPlus 12233) - 2 / (12233 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12233 * (kappa (meanLowerRoot 12233 θ ^ 2 / gPlus 12233) -
        2 / (12233 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12233) / 12233 -
        finiteEnergy 12233 12233 (11 / 1000) / √12233 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12233 θ ^ 2 / gPlus 12233 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12233)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12233 θ ^ 2 / gPlus 12233 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12233)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12233 θ ^ 2 / gPlus 12233 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12233 ^ 2 ≤
      kappa (meanLowerRoot 12233 θ ^ 2 / gPlus 12233) - 2 / (12233 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12233 *
      (kappa (meanLowerRoot 12233 θ ^ 2 / gPlus 12233) - 2 / (12233 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12233 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12233)
    linarith
  have ht : √(12 * gPlus 12233) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12233 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12233 12233 (11 / 1000) / √12233 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12233)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12233 (gMinus 12233) (gPlus 12233)
      (finiteEnergy 12233 12233 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12233) (hτ : 0 < (paperDesignP 12233).tau0 c) :
    eR c = (2 / (mA 12233 : ℝ)) *
      normSq (BstLean.Part150.bT 12233 12233 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12233).tau0 c)) /
      (2 / (12233 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12233).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12233).tau0 c))⁻¹ •
      BstLean.Part150.bT 12233 12233 (A1 c) (A2 c) c.1.2 ((paperDesignP 12233).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12233 : ℝ)) * normSq (bR c) / (2 / (12233 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12233}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12233) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12233).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12233 : ℝ) * (paperDesignP 12233).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12233 12233 c.1.2 ((paperDesignP 12233).tau0 c) :=
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

end BstLean.Part262.Row12233

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12234 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12234).real (BstLean.Part211.CentreSource 12234 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12234) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12234 160 (6 / 1000)
  have hj := jS_160_le (n := 12234) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12234 160 (6 / 1000) ^ 2 * 12234 /
      (((12234 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12234 160 (6 / 1000) ^ 2 * 12234 /
      (((12234 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12234 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12234 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12234) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12234 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12234

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12234) :=
  Ethm (paperCentres 12234) ∩ Ethp (paperCentres 12234)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12234)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12234)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12234) (paperCentres 12234)
  have he : exp (-(45 / 10000 * (12234 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12234 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12234) :=
  (passEvent ∩ agentEv (paperDesignP 12234) (DirectionError 12234) ∩
    agentEv (paperDesignP 12234) (CentreSources 12234 12234)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12234)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12234) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12234) hτ
  have hC := centreSources_ret_charge_row 12234 (paperDesignP 12234) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12234)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12234) (CentreSources 12234 12234)
  direction : analyticBase ⊆ agentEv (paperDesignP 12234) (DirectionError 12234)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12234)) : Set (Ret 12234) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12234)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12234)}
    (hT : (retDist (paperCentres 12234)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12234)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12234)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12234)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12234)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12234)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12234

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12234 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12234 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12234 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12234 12234 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12234)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12234)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12234
  have hb0 := BstLean.Part150.betaJ_nonneg 12234
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12234 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12234 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12234 * BstLean.Part150.betaJ 12234) * 12234) ≤
      (31456311 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12234)) * 12234 := by gcongr <;> linarith
      _ ≤ ((31456311 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12234 * 12234 *
      (1 + BstLean.Part154.deltaChi 12234 12 + 2 / π) / BstLean.Part154.csC) ≤
      (36005557 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12234 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((36005557 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12234 : ℝ) / BstLean.Part154.csC) ≤ (6074271 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12234 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((6074271 / 62500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12234 : ℝ) * (31456311 / 200000) +
        2 * (1792 / 10000 / 12234) * (36005557 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (6074271 / 62500) *
          (81 / 1000 / 12234 + (1792 / 10000 / 12234) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12234

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12234
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12234 ∧
    1 ≤ gPlus 12234 ∧ gPlus 12234 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12234 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12234 : ℝ) < √(1 - 2 / (12234 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12234 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12234 (gMinus 12234) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12234 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12234 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12234 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12234)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12234 (gMinus 12234) (gPlus 12234)
      (finiteEnergy 12234 12234 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12234 (gMinus 12234) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12234 (gMinus 12234) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12234 (gMinus 12234) (54 / 100))
    (by linarith : energyRatio 12234 (gMinus 12234) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12234 (gMinus 12234) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12234 * kappa (energyRatio 12234 (gMinus 12234) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12234) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12234 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12234 12234 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12234 12234 (11 / 1000) / √12234 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12234)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12234 * kappa (energyRatio 12234 (gMinus 12234) (54 / 100))) +
      2 * √(12 * gPlus 12234) / 12234 + finiteEnergy 12234 12234 (11 / 1000) / √12234 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12234 θ ∧ meanLowerRoot 12234 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12234 - 2 / (12234 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12234 - 2 / (12234 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12234 θ ^ 2 / gPlus 12234) - 2 / (12234 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12234 * (kappa (meanLowerRoot 12234 θ ^ 2 / gPlus 12234) -
        2 / (12234 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12234) / 12234 -
        finiteEnergy 12234 12234 (11 / 1000) / √12234 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12234 θ ^ 2 / gPlus 12234 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12234)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12234 θ ^ 2 / gPlus 12234 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12234)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12234 θ ^ 2 / gPlus 12234 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12234 ^ 2 ≤
      kappa (meanLowerRoot 12234 θ ^ 2 / gPlus 12234) - 2 / (12234 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12234 *
      (kappa (meanLowerRoot 12234 θ ^ 2 / gPlus 12234) - 2 / (12234 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12234 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12234)
    linarith
  have ht : √(12 * gPlus 12234) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12234 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12234 12234 (11 / 1000) / √12234 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12234)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12234 (gMinus 12234) (gPlus 12234)
      (finiteEnergy 12234 12234 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12234) (hτ : 0 < (paperDesignP 12234).tau0 c) :
    eR c = (2 / (mA 12234 : ℝ)) *
      normSq (BstLean.Part150.bT 12234 12234 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12234).tau0 c)) /
      (2 / (12234 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12234).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12234).tau0 c))⁻¹ •
      BstLean.Part150.bT 12234 12234 (A1 c) (A2 c) c.1.2 ((paperDesignP 12234).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12234 : ℝ)) * normSq (bR c) / (2 / (12234 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12234}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12234) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12234).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12234 : ℝ) * (paperDesignP 12234).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12234 12234 c.1.2 ((paperDesignP 12234).tau0 c) :=
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

end BstLean.Part262.Row12234

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12235 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12235).real (BstLean.Part211.CentreSource 12235 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12235) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12235 160 (6 / 1000)
  have hj := jS_160_le (n := 12235) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12235 160 (6 / 1000) ^ 2 * 12235 /
      (((12235 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12235 160 (6 / 1000) ^ 2 * 12235 /
      (((12235 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12235 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12235 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12235) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12235 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12235

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12235) :=
  Ethm (paperCentres 12235) ∩ Ethp (paperCentres 12235)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12235)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12235)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12235) (paperCentres 12235)
  have he : exp (-(45 / 10000 * (12235 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12235 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12235) :=
  (passEvent ∩ agentEv (paperDesignP 12235) (DirectionError 12235) ∩
    agentEv (paperDesignP 12235) (CentreSources 12235 12235)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12235)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12235) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12235) hτ
  have hC := centreSources_ret_charge_row 12235 (paperDesignP 12235) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12235)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12235) (CentreSources 12235 12235)
  direction : analyticBase ⊆ agentEv (paperDesignP 12235) (DirectionError 12235)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12235)) : Set (Ret 12235) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12235)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12235)}
    (hT : (retDist (paperCentres 12235)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12235)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12235)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12235)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12235)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12235)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12235

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12235 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12235 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12235 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12235 12235 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12235)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12235)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12235
  have hb0 := BstLean.Part150.betaJ_nonneg 12235
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12235 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12235 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12235 * BstLean.Part150.betaJ 12235) * 12235) ≤
      (157287983 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12235)) * 12235 := by gcongr <;> linarith
      _ ≤ ((157287983 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12235 * 12235 *
      (1 + BstLean.Part154.deltaChi 12235 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180035143 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12235 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180035143 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12235 : ℝ) / BstLean.Part154.csC) ≤ (24298077 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12235 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((24298077 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12235 : ℝ) * (157287983 / 1000000) +
        2 * (1792 / 10000 / 12235) * (180035143 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (24298077 / 250000) *
          (81 / 1000 / 12235 + (1792 / 10000 / 12235) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12235

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12235
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12235 ∧
    1 ≤ gPlus 12235 ∧ gPlus 12235 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12235 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12235 : ℝ) < √(1 - 2 / (12235 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12235 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12235 (gMinus 12235) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12235 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12235 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12235 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12235)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12235 (gMinus 12235) (gPlus 12235)
      (finiteEnergy 12235 12235 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12235 (gMinus 12235) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12235 (gMinus 12235) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12235 (gMinus 12235) (54 / 100))
    (by linarith : energyRatio 12235 (gMinus 12235) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12235 (gMinus 12235) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12235 * kappa (energyRatio 12235 (gMinus 12235) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12235) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12235 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12235 12235 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12235 12235 (11 / 1000) / √12235 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12235)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12235 * kappa (energyRatio 12235 (gMinus 12235) (54 / 100))) +
      2 * √(12 * gPlus 12235) / 12235 + finiteEnergy 12235 12235 (11 / 1000) / √12235 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12235 θ ∧ meanLowerRoot 12235 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12235 - 2 / (12235 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12235 - 2 / (12235 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12235 θ ^ 2 / gPlus 12235) - 2 / (12235 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12235 * (kappa (meanLowerRoot 12235 θ ^ 2 / gPlus 12235) -
        2 / (12235 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12235) / 12235 -
        finiteEnergy 12235 12235 (11 / 1000) / √12235 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12235 θ ^ 2 / gPlus 12235 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12235)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12235 θ ^ 2 / gPlus 12235 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12235)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12235 θ ^ 2 / gPlus 12235 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12235 ^ 2 ≤
      kappa (meanLowerRoot 12235 θ ^ 2 / gPlus 12235) - 2 / (12235 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12235 *
      (kappa (meanLowerRoot 12235 θ ^ 2 / gPlus 12235) - 2 / (12235 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12235 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12235)
    linarith
  have ht : √(12 * gPlus 12235) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12235 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12235 12235 (11 / 1000) / √12235 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12235)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12235 (gMinus 12235) (gPlus 12235)
      (finiteEnergy 12235 12235 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12235) (hτ : 0 < (paperDesignP 12235).tau0 c) :
    eR c = (2 / (mA 12235 : ℝ)) *
      normSq (BstLean.Part150.bT 12235 12235 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12235).tau0 c)) /
      (2 / (12235 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12235).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12235).tau0 c))⁻¹ •
      BstLean.Part150.bT 12235 12235 (A1 c) (A2 c) c.1.2 ((paperDesignP 12235).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12235 : ℝ)) * normSq (bR c) / (2 / (12235 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12235}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12235) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12235).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12235 : ℝ) * (paperDesignP 12235).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12235 12235 c.1.2 ((paperDesignP 12235).tau0 c) :=
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

end BstLean.Part262.Row12235

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12236 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12236).real (BstLean.Part211.CentreSource 12236 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12236) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12236 160 (6 / 1000)
  have hj := jS_160_le (n := 12236) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12236 160 (6 / 1000) ^ 2 * 12236 /
      (((12236 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12236 160 (6 / 1000) ^ 2 * 12236 /
      (((12236 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12236 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12236 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12236) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12236 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12236

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12236) :=
  Ethm (paperCentres 12236) ∩ Ethp (paperCentres 12236)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12236)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12236)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12236) (paperCentres 12236)
  have he : exp (-(45 / 10000 * (12236 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12236 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12236) :=
  (passEvent ∩ agentEv (paperDesignP 12236) (DirectionError 12236) ∩
    agentEv (paperDesignP 12236) (CentreSources 12236 12236)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12236)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12236) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12236) hτ
  have hC := centreSources_ret_charge_row 12236 (paperDesignP 12236) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12236)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12236) (CentreSources 12236 12236)
  direction : analyticBase ⊆ agentEv (paperDesignP 12236) (DirectionError 12236)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12236)) : Set (Ret 12236) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12236)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12236)}
    (hT : (retDist (paperCentres 12236)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12236)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12236)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12236)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12236)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12236)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12236

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12236 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12236 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12236 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12236 12236 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12236)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12236)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12236
  have hb0 := BstLean.Part150.betaJ_nonneg 12236
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12236 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12236 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12236 * BstLean.Part150.betaJ 12236) * 12236) ≤
      (157294411 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12236)) * 12236 := by gcongr <;> linarith
      _ ≤ ((157294411 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12236 * 12236 *
      (1 + BstLean.Part154.deltaChi 12236 12 + 2 / π) / BstLean.Part154.csC) ≤
      (72017 / 400) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12236 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((72017 / 400) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12236 : ℝ) / BstLean.Part154.csC) ≤ (2429907 / 25000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12236 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((2429907 / 25000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12236 : ℝ) * (157294411 / 1000000) +
        2 * (1792 / 10000 / 12236) * (72017 / 400) +
        4 * (1 / 2.506628) * 1.036505 * (2429907 / 25000) *
          (81 / 1000 / 12236 + (1792 / 10000 / 12236) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12236

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12236
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12236 ∧
    1 ≤ gPlus 12236 ∧ gPlus 12236 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12236 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12236 : ℝ) < √(1 - 2 / (12236 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12236 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12236 (gMinus 12236) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12236 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12236 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12236 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12236)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12236 (gMinus 12236) (gPlus 12236)
      (finiteEnergy 12236 12236 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12236 (gMinus 12236) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12236 (gMinus 12236) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12236 (gMinus 12236) (54 / 100))
    (by linarith : energyRatio 12236 (gMinus 12236) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12236 (gMinus 12236) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12236 * kappa (energyRatio 12236 (gMinus 12236) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12236) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12236 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12236 12236 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12236 12236 (11 / 1000) / √12236 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12236)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12236 * kappa (energyRatio 12236 (gMinus 12236) (54 / 100))) +
      2 * √(12 * gPlus 12236) / 12236 + finiteEnergy 12236 12236 (11 / 1000) / √12236 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12236 θ ∧ meanLowerRoot 12236 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12236 - 2 / (12236 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12236 - 2 / (12236 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12236 θ ^ 2 / gPlus 12236) - 2 / (12236 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12236 * (kappa (meanLowerRoot 12236 θ ^ 2 / gPlus 12236) -
        2 / (12236 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12236) / 12236 -
        finiteEnergy 12236 12236 (11 / 1000) / √12236 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12236 θ ^ 2 / gPlus 12236 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12236)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12236 θ ^ 2 / gPlus 12236 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12236)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12236 θ ^ 2 / gPlus 12236 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12236 ^ 2 ≤
      kappa (meanLowerRoot 12236 θ ^ 2 / gPlus 12236) - 2 / (12236 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12236 *
      (kappa (meanLowerRoot 12236 θ ^ 2 / gPlus 12236) - 2 / (12236 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12236 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12236)
    linarith
  have ht : √(12 * gPlus 12236) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12236 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12236 12236 (11 / 1000) / √12236 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12236)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12236 (gMinus 12236) (gPlus 12236)
      (finiteEnergy 12236 12236 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12236) (hτ : 0 < (paperDesignP 12236).tau0 c) :
    eR c = (2 / (mA 12236 : ℝ)) *
      normSq (BstLean.Part150.bT 12236 12236 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12236).tau0 c)) /
      (2 / (12236 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12236).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12236).tau0 c))⁻¹ •
      BstLean.Part150.bT 12236 12236 (A1 c) (A2 c) c.1.2 ((paperDesignP 12236).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12236 : ℝ)) * normSq (bR c) / (2 / (12236 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12236}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12236) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12236).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12236 : ℝ) * (paperDesignP 12236).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12236 12236 c.1.2 ((paperDesignP 12236).tau0 c) :=
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

end BstLean.Part262.Row12236

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12237 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12237).real (BstLean.Part211.CentreSource 12237 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12237) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12237 160 (6 / 1000)
  have hj := jS_160_le (n := 12237) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12237 160 (6 / 1000) ^ 2 * 12237 /
      (((12237 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12237 160 (6 / 1000) ^ 2 * 12237 /
      (((12237 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12237 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12237 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12237) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12237 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12237

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12237) :=
  Ethm (paperCentres 12237) ∩ Ethp (paperCentres 12237)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12237)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12237)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12237) (paperCentres 12237)
  have he : exp (-(45 / 10000 * (12237 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12237 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12237) :=
  (passEvent ∩ agentEv (paperDesignP 12237) (DirectionError 12237) ∩
    agentEv (paperDesignP 12237) (CentreSources 12237 12237)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12237)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12237) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12237) hτ
  have hC := centreSources_ret_charge_row 12237 (paperDesignP 12237) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12237)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12237) (CentreSources 12237 12237)
  direction : analyticBase ⊆ agentEv (paperDesignP 12237) (DirectionError 12237)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12237)) : Set (Ret 12237) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12237)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12237)}
    (hT : (retDist (paperCentres 12237)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12237)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12237)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12237)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12237)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12237)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12237

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12237 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12237 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12237 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12237 12237 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12237)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12237)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12237
  have hb0 := BstLean.Part150.betaJ_nonneg 12237
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12237 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12237 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12237 * BstLean.Part150.betaJ 12237) * 12237) ≤
      (78650419 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12237)) * 12237 := by gcongr <;> linarith
      _ ≤ ((78650419 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12237 * 12237 *
      (1 + BstLean.Part154.deltaChi 12237 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180049857 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12237 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180049857 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12237 : ℝ) / BstLean.Part154.csC) ≤ (97200251 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12237 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97200251 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12237 : ℝ) * (78650419 / 500000) +
        2 * (1792 / 10000 / 12237) * (180049857 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97200251 / 1000000) *
          (81 / 1000 / 12237 + (1792 / 10000 / 12237) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12237

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12237
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12237 ∧
    1 ≤ gPlus 12237 ∧ gPlus 12237 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12237 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12237 : ℝ) < √(1 - 2 / (12237 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12237 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12237 (gMinus 12237) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12237 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12237 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12237 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12237)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12237 (gMinus 12237) (gPlus 12237)
      (finiteEnergy 12237 12237 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12237 (gMinus 12237) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12237 (gMinus 12237) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12237 (gMinus 12237) (54 / 100))
    (by linarith : energyRatio 12237 (gMinus 12237) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12237 (gMinus 12237) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12237 * kappa (energyRatio 12237 (gMinus 12237) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12237) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12237 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12237 12237 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12237 12237 (11 / 1000) / √12237 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12237)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12237 * kappa (energyRatio 12237 (gMinus 12237) (54 / 100))) +
      2 * √(12 * gPlus 12237) / 12237 + finiteEnergy 12237 12237 (11 / 1000) / √12237 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12237 θ ∧ meanLowerRoot 12237 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12237 - 2 / (12237 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12237 - 2 / (12237 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12237 θ ^ 2 / gPlus 12237) - 2 / (12237 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12237 * (kappa (meanLowerRoot 12237 θ ^ 2 / gPlus 12237) -
        2 / (12237 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12237) / 12237 -
        finiteEnergy 12237 12237 (11 / 1000) / √12237 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12237 θ ^ 2 / gPlus 12237 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12237)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12237 θ ^ 2 / gPlus 12237 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12237)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12237 θ ^ 2 / gPlus 12237 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12237 ^ 2 ≤
      kappa (meanLowerRoot 12237 θ ^ 2 / gPlus 12237) - 2 / (12237 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12237 *
      (kappa (meanLowerRoot 12237 θ ^ 2 / gPlus 12237) - 2 / (12237 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12237 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12237)
    linarith
  have ht : √(12 * gPlus 12237) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12237 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12237 12237 (11 / 1000) / √12237 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12237)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12237 (gMinus 12237) (gPlus 12237)
      (finiteEnergy 12237 12237 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12237) (hτ : 0 < (paperDesignP 12237).tau0 c) :
    eR c = (2 / (mA 12237 : ℝ)) *
      normSq (BstLean.Part150.bT 12237 12237 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12237).tau0 c)) /
      (2 / (12237 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12237).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12237).tau0 c))⁻¹ •
      BstLean.Part150.bT 12237 12237 (A1 c) (A2 c) c.1.2 ((paperDesignP 12237).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12237 : ℝ)) * normSq (bR c) / (2 / (12237 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12237}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12237) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12237).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12237 : ℝ) * (paperDesignP 12237).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12237 12237 c.1.2 ((paperDesignP 12237).tau0 c) :=
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

end BstLean.Part262.Row12237

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12238 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12238).real (BstLean.Part211.CentreSource 12238 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12238) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12238 160 (6 / 1000)
  have hj := jS_160_le (n := 12238) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12238 160 (6 / 1000) ^ 2 * 12238 /
      (((12238 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12238 160 (6 / 1000) ^ 2 * 12238 /
      (((12238 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12238 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12238 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12238) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12238 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12238

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12238) :=
  Ethm (paperCentres 12238) ∩ Ethp (paperCentres 12238)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12238)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12238)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12238) (paperCentres 12238)
  have he : exp (-(45 / 10000 * (12238 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12238 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12238) :=
  (passEvent ∩ agentEv (paperDesignP 12238) (DirectionError 12238) ∩
    agentEv (paperDesignP 12238) (CentreSources 12238 12238)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12238)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12238) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12238) hτ
  have hC := centreSources_ret_charge_row 12238 (paperDesignP 12238) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12238)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12238) (CentreSources 12238 12238)
  direction : analyticBase ⊆ agentEv (paperDesignP 12238) (DirectionError 12238)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12238)) : Set (Ret 12238) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12238)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12238)}
    (hT : (retDist (paperCentres 12238)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12238)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12238)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12238)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12238)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12238)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12238

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12238 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12238 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12238 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12238 12238 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12238)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12238)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12238
  have hb0 := BstLean.Part150.betaJ_nonneg 12238
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12238 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12238 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12238 * BstLean.Part150.betaJ 12238) * 12238) ≤
      (31461453 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12238)) * 12238 := by gcongr <;> linarith
      _ ≤ ((31461453 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12238 * 12238 *
      (1 + BstLean.Part154.deltaChi 12238 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90028607 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12238 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90028607 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12238 : ℝ) / BstLean.Part154.csC) ≤ (97204223 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12238 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97204223 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12238 : ℝ) * (31461453 / 200000) +
        2 * (1792 / 10000 / 12238) * (90028607 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (97204223 / 1000000) *
          (81 / 1000 / 12238 + (1792 / 10000 / 12238) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12238

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12238
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12238 ∧
    1 ≤ gPlus 12238 ∧ gPlus 12238 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12238 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12238 : ℝ) < √(1 - 2 / (12238 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12238 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12238 (gMinus 12238) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12238 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12238 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12238 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12238)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12238 (gMinus 12238) (gPlus 12238)
      (finiteEnergy 12238 12238 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12238 (gMinus 12238) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12238 (gMinus 12238) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12238 (gMinus 12238) (54 / 100))
    (by linarith : energyRatio 12238 (gMinus 12238) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12238 (gMinus 12238) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12238 * kappa (energyRatio 12238 (gMinus 12238) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12238) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12238 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12238 12238 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12238 12238 (11 / 1000) / √12238 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12238)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12238 * kappa (energyRatio 12238 (gMinus 12238) (54 / 100))) +
      2 * √(12 * gPlus 12238) / 12238 + finiteEnergy 12238 12238 (11 / 1000) / √12238 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12238 θ ∧ meanLowerRoot 12238 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12238 - 2 / (12238 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12238 - 2 / (12238 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12238 θ ^ 2 / gPlus 12238) - 2 / (12238 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12238 * (kappa (meanLowerRoot 12238 θ ^ 2 / gPlus 12238) -
        2 / (12238 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12238) / 12238 -
        finiteEnergy 12238 12238 (11 / 1000) / √12238 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12238 θ ^ 2 / gPlus 12238 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12238)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12238 θ ^ 2 / gPlus 12238 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12238)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12238 θ ^ 2 / gPlus 12238 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12238 ^ 2 ≤
      kappa (meanLowerRoot 12238 θ ^ 2 / gPlus 12238) - 2 / (12238 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12238 *
      (kappa (meanLowerRoot 12238 θ ^ 2 / gPlus 12238) - 2 / (12238 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12238 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12238)
    linarith
  have ht : √(12 * gPlus 12238) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12238 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12238 12238 (11 / 1000) / √12238 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12238)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12238 (gMinus 12238) (gPlus 12238)
      (finiteEnergy 12238 12238 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12238) (hτ : 0 < (paperDesignP 12238).tau0 c) :
    eR c = (2 / (mA 12238 : ℝ)) *
      normSq (BstLean.Part150.bT 12238 12238 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12238).tau0 c)) /
      (2 / (12238 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12238).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12238).tau0 c))⁻¹ •
      BstLean.Part150.bT 12238 12238 (A1 c) (A2 c) c.1.2 ((paperDesignP 12238).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12238 : ℝ)) * normSq (bR c) / (2 / (12238 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12238}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12238) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12238).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12238 : ℝ) * (paperDesignP 12238).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12238 12238 c.1.2 ((paperDesignP 12238).tau0 c) :=
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

end BstLean.Part262.Row12238

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12239 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12239).real (BstLean.Part211.CentreSource 12239 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12239) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12239 160 (6 / 1000)
  have hj := jS_160_le (n := 12239) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12239 160 (6 / 1000) ^ 2 * 12239 /
      (((12239 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12239 160 (6 / 1000) ^ 2 * 12239 /
      (((12239 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12239 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12239 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12239) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12239 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12239

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12239) :=
  Ethm (paperCentres 12239) ∩ Ethp (paperCentres 12239)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12239)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12239)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12239) (paperCentres 12239)
  have he : exp (-(45 / 10000 * (12239 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12239 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12239) :=
  (passEvent ∩ agentEv (paperDesignP 12239) (DirectionError 12239) ∩
    agentEv (paperDesignP 12239) (CentreSources 12239 12239)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12239)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12239) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12239) hτ
  have hC := centreSources_ret_charge_row 12239 (paperDesignP 12239) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12239)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12239) (CentreSources 12239 12239)
  direction : analyticBase ⊆ agentEv (paperDesignP 12239) (DirectionError 12239)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12239)) : Set (Ret 12239) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12239)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12239)}
    (hT : (retDist (paperCentres 12239)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12239)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12239)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12239)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12239)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12239)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12239

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12239 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12239 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12239 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12239 12239 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12239)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12239)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12239
  have hb0 := BstLean.Part150.betaJ_nonneg 12239
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12239 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12239 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12239 * BstLean.Part150.betaJ 12239) * 12239) ≤
      (39328423 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12239)) * 12239 := by gcongr <;> linarith
      _ ≤ ((39328423 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12239 * 12239 *
      (1 + BstLean.Part154.deltaChi 12239 12 + 2 / π) / BstLean.Part154.csC) ≤
      (18006457 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12239 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((18006457 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12239 : ℝ) / BstLean.Part154.csC) ≤ (48604097 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12239 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48604097 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12239 : ℝ) * (39328423 / 250000) +
        2 * (1792 / 10000 / 12239) * (18006457 / 100000) +
        4 * (1 / 2.506628) * 1.036505 * (48604097 / 500000) *
          (81 / 1000 / 12239 + (1792 / 10000 / 12239) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12239

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12239
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12239 ∧
    1 ≤ gPlus 12239 ∧ gPlus 12239 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12239 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12239 : ℝ) < √(1 - 2 / (12239 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12239 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12239 (gMinus 12239) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12239 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12239 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12239 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12239)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12239 (gMinus 12239) (gPlus 12239)
      (finiteEnergy 12239 12239 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12239 (gMinus 12239) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12239 (gMinus 12239) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12239 (gMinus 12239) (54 / 100))
    (by linarith : energyRatio 12239 (gMinus 12239) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12239 (gMinus 12239) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12239 * kappa (energyRatio 12239 (gMinus 12239) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12239) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12239 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12239 12239 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12239 12239 (11 / 1000) / √12239 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12239)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12239 * kappa (energyRatio 12239 (gMinus 12239) (54 / 100))) +
      2 * √(12 * gPlus 12239) / 12239 + finiteEnergy 12239 12239 (11 / 1000) / √12239 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12239 θ ∧ meanLowerRoot 12239 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12239 - 2 / (12239 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12239 - 2 / (12239 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12239 θ ^ 2 / gPlus 12239) - 2 / (12239 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12239 * (kappa (meanLowerRoot 12239 θ ^ 2 / gPlus 12239) -
        2 / (12239 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12239) / 12239 -
        finiteEnergy 12239 12239 (11 / 1000) / √12239 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12239 θ ^ 2 / gPlus 12239 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12239)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12239 θ ^ 2 / gPlus 12239 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12239)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12239 θ ^ 2 / gPlus 12239 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12239 ^ 2 ≤
      kappa (meanLowerRoot 12239 θ ^ 2 / gPlus 12239) - 2 / (12239 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12239 *
      (kappa (meanLowerRoot 12239 θ ^ 2 / gPlus 12239) - 2 / (12239 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12239 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12239)
    linarith
  have ht : √(12 * gPlus 12239) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12239 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12239 12239 (11 / 1000) / √12239 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12239)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12239 (gMinus 12239) (gPlus 12239)
      (finiteEnergy 12239 12239 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12239) (hτ : 0 < (paperDesignP 12239).tau0 c) :
    eR c = (2 / (mA 12239 : ℝ)) *
      normSq (BstLean.Part150.bT 12239 12239 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12239).tau0 c)) /
      (2 / (12239 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12239).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12239).tau0 c))⁻¹ •
      BstLean.Part150.bT 12239 12239 (A1 c) (A2 c) c.1.2 ((paperDesignP 12239).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12239 : ℝ)) * normSq (bR c) / (2 / (12239 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12239}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12239) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12239).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12239 : ℝ) * (paperDesignP 12239).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12239 12239 c.1.2 ((paperDesignP 12239).tau0 c) :=
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

end BstLean.Part262.Row12239

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12240 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12240).real (BstLean.Part211.CentreSource 12240 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12240) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12240 160 (6 / 1000)
  have hj := jS_160_le (n := 12240) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12240 160 (6 / 1000) ^ 2 * 12240 /
      (((12240 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12240 160 (6 / 1000) ^ 2 * 12240 /
      (((12240 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12240 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12240 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12240) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12240 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12240

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12240) :=
  Ethm (paperCentres 12240) ∩ Ethp (paperCentres 12240)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12240)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12240)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12240) (paperCentres 12240)
  have he : exp (-(45 / 10000 * (12240 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12240 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12240) :=
  (passEvent ∩ agentEv (paperDesignP 12240) (DirectionError 12240) ∩
    agentEv (paperDesignP 12240) (CentreSources 12240 12240)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12240)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12240) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12240) hτ
  have hC := centreSources_ret_charge_row 12240 (paperDesignP 12240) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12240)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12240) (CentreSources 12240 12240)
  direction : analyticBase ⊆ agentEv (paperDesignP 12240) (DirectionError 12240)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12240)) : Set (Ret 12240) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12240)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12240)}
    (hT : (retDist (paperCentres 12240)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12240)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12240)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12240)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12240)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12240)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12240

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12240 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12240 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12240 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12240 12240 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12240)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12240)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12240
  have hb0 := BstLean.Part150.betaJ_nonneg 12240
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12240 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12240 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12240 * BstLean.Part150.betaJ 12240) * 12240) ≤
      (78660059 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12240)) * 12240 := by gcongr <;> linarith
      _ ≤ ((78660059 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12240 * 12240 *
      (1 + BstLean.Part154.deltaChi 12240 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90035963 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12240 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90035963 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12240 : ℝ) / BstLean.Part154.csC) ≤ (19442433 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12240 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19442433 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12240 : ℝ) * (78660059 / 500000) +
        2 * (1792 / 10000 / 12240) * (90035963 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (19442433 / 200000) *
          (81 / 1000 / 12240 + (1792 / 10000 / 12240) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12240

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12240
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12240 ∧
    1 ≤ gPlus 12240 ∧ gPlus 12240 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12240 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12240 : ℝ) < √(1 - 2 / (12240 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12240 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12240 (gMinus 12240) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12240 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12240 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12240 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12240)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12240 (gMinus 12240) (gPlus 12240)
      (finiteEnergy 12240 12240 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12240 (gMinus 12240) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12240 (gMinus 12240) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12240 (gMinus 12240) (54 / 100))
    (by linarith : energyRatio 12240 (gMinus 12240) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12240 (gMinus 12240) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12240 * kappa (energyRatio 12240 (gMinus 12240) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12240) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12240 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12240 12240 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12240 12240 (11 / 1000) / √12240 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12240)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12240 * kappa (energyRatio 12240 (gMinus 12240) (54 / 100))) +
      2 * √(12 * gPlus 12240) / 12240 + finiteEnergy 12240 12240 (11 / 1000) / √12240 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12240 θ ∧ meanLowerRoot 12240 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12240 - 2 / (12240 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12240 - 2 / (12240 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12240 θ ^ 2 / gPlus 12240) - 2 / (12240 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12240 * (kappa (meanLowerRoot 12240 θ ^ 2 / gPlus 12240) -
        2 / (12240 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12240) / 12240 -
        finiteEnergy 12240 12240 (11 / 1000) / √12240 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12240 θ ^ 2 / gPlus 12240 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12240)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12240 θ ^ 2 / gPlus 12240 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12240)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12240 θ ^ 2 / gPlus 12240 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12240 ^ 2 ≤
      kappa (meanLowerRoot 12240 θ ^ 2 / gPlus 12240) - 2 / (12240 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12240 *
      (kappa (meanLowerRoot 12240 θ ^ 2 / gPlus 12240) - 2 / (12240 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12240 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12240)
    linarith
  have ht : √(12 * gPlus 12240) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12240 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12240 12240 (11 / 1000) / √12240 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12240)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12240 (gMinus 12240) (gPlus 12240)
      (finiteEnergy 12240 12240 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12240) (hτ : 0 < (paperDesignP 12240).tau0 c) :
    eR c = (2 / (mA 12240 : ℝ)) *
      normSq (BstLean.Part150.bT 12240 12240 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12240).tau0 c)) /
      (2 / (12240 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12240).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12240).tau0 c))⁻¹ •
      BstLean.Part150.bT 12240 12240 (A1 c) (A2 c) c.1.2 ((paperDesignP 12240).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12240 : ℝ)) * normSq (bR c) / (2 / (12240 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12240}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12240) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12240).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12240 : ℝ) * (paperDesignP 12240).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12240 12240 c.1.2 ((paperDesignP 12240).tau0 c) :=
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

end BstLean.Part262.Row12240

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12241 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12241).real (BstLean.Part211.CentreSource 12241 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12241) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12241 160 (6 / 1000)
  have hj := jS_160_le (n := 12241) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12241 160 (6 / 1000) ^ 2 * 12241 /
      (((12241 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12241 160 (6 / 1000) ^ 2 * 12241 /
      (((12241 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12241 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12241 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12241) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12241 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12241

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12241) :=
  Ethm (paperCentres 12241) ∩ Ethp (paperCentres 12241)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12241)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12241)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12241) (paperCentres 12241)
  have he : exp (-(45 / 10000 * (12241 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12241 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12241) :=
  (passEvent ∩ agentEv (paperDesignP 12241) (DirectionError 12241) ∩
    agentEv (paperDesignP 12241) (CentreSources 12241 12241)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12241)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12241) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12241) hτ
  have hC := centreSources_ret_charge_row 12241 (paperDesignP 12241) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12241)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12241) (CentreSources 12241 12241)
  direction : analyticBase ⊆ agentEv (paperDesignP 12241) (DirectionError 12241)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12241)) : Set (Ret 12241) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12241)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12241)}
    (hT : (retDist (paperCentres 12241)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12241)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12241)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12241)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12241)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12241)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12241

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12241 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12241 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12241 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12241 12241 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12241)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12241)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12241
  have hb0 := BstLean.Part150.betaJ_nonneg 12241
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12241 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12241 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12241 * BstLean.Part150.betaJ 12241) * 12241) ≤
      (31465309 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12241)) * 12241 := by gcongr <;> linarith
      _ ≤ ((31465309 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12241 * 12241 *
      (1 + BstLean.Part154.deltaChi 12241 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90039641 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12241 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90039641 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12241 : ℝ) / BstLean.Part154.csC) ≤ (12152017 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12241 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12152017 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12241 : ℝ) * (31465309 / 200000) +
        2 * (1792 / 10000 / 12241) * (90039641 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (12152017 / 125000) *
          (81 / 1000 / 12241 + (1792 / 10000 / 12241) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12241

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12241
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12241 ∧
    1 ≤ gPlus 12241 ∧ gPlus 12241 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12241 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12241 : ℝ) < √(1 - 2 / (12241 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12241 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12241 (gMinus 12241) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12241 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12241 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12241 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12241)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12241 (gMinus 12241) (gPlus 12241)
      (finiteEnergy 12241 12241 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12241 (gMinus 12241) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12241 (gMinus 12241) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12241 (gMinus 12241) (54 / 100))
    (by linarith : energyRatio 12241 (gMinus 12241) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12241 (gMinus 12241) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12241 * kappa (energyRatio 12241 (gMinus 12241) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12241) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12241 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12241 12241 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12241 12241 (11 / 1000) / √12241 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12241)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12241 * kappa (energyRatio 12241 (gMinus 12241) (54 / 100))) +
      2 * √(12 * gPlus 12241) / 12241 + finiteEnergy 12241 12241 (11 / 1000) / √12241 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12241 θ ∧ meanLowerRoot 12241 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12241 - 2 / (12241 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12241 - 2 / (12241 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12241 θ ^ 2 / gPlus 12241) - 2 / (12241 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12241 * (kappa (meanLowerRoot 12241 θ ^ 2 / gPlus 12241) -
        2 / (12241 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12241) / 12241 -
        finiteEnergy 12241 12241 (11 / 1000) / √12241 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12241 θ ^ 2 / gPlus 12241 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12241)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12241 θ ^ 2 / gPlus 12241 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12241)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12241 θ ^ 2 / gPlus 12241 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12241 ^ 2 ≤
      kappa (meanLowerRoot 12241 θ ^ 2 / gPlus 12241) - 2 / (12241 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12241 *
      (kappa (meanLowerRoot 12241 θ ^ 2 / gPlus 12241) - 2 / (12241 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12241 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12241)
    linarith
  have ht : √(12 * gPlus 12241) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12241 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12241 12241 (11 / 1000) / √12241 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12241)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12241 (gMinus 12241) (gPlus 12241)
      (finiteEnergy 12241 12241 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12241) (hτ : 0 < (paperDesignP 12241).tau0 c) :
    eR c = (2 / (mA 12241 : ℝ)) *
      normSq (BstLean.Part150.bT 12241 12241 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12241).tau0 c)) /
      (2 / (12241 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12241).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12241).tau0 c))⁻¹ •
      BstLean.Part150.bT 12241 12241 (A1 c) (A2 c) c.1.2 ((paperDesignP 12241).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12241 : ℝ)) * normSq (bR c) / (2 / (12241 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12241}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12241) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12241).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12241 : ℝ) * (paperDesignP 12241).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12241 12241 c.1.2 ((paperDesignP 12241).tau0 c) :=
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

end BstLean.Part262.Row12241

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12242 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12242).real (BstLean.Part211.CentreSource 12242 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12242) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12242 160 (6 / 1000)
  have hj := jS_160_le (n := 12242) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12242 160 (6 / 1000) ^ 2 * 12242 /
      (((12242 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12242 160 (6 / 1000) ^ 2 * 12242 /
      (((12242 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12242 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12242 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12242) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12242 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12242

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12242) :=
  Ethm (paperCentres 12242) ∩ Ethp (paperCentres 12242)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12242)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12242)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12242) (paperCentres 12242)
  have he : exp (-(45 / 10000 * (12242 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12242 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12242) :=
  (passEvent ∩ agentEv (paperDesignP 12242) (DirectionError 12242) ∩
    agentEv (paperDesignP 12242) (CentreSources 12242 12242)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12242)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12242) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12242) hτ
  have hC := centreSources_ret_charge_row 12242 (paperDesignP 12242) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12242)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12242) (CentreSources 12242 12242)
  direction : analyticBase ⊆ agentEv (paperDesignP 12242) (DirectionError 12242)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12242)) : Set (Ret 12242) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12242)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12242)}
    (hT : (retDist (paperCentres 12242)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12242)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12242)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12242)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12242)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12242)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12242

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12242 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12242 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12242 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12242 12242 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12242)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12242)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12242
  have hb0 := BstLean.Part150.betaJ_nonneg 12242
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12242 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12242 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12242 * BstLean.Part150.betaJ 12242) * 12242) ≤
      (157332971 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12242)) * 12242 := by gcongr <;> linarith
      _ ≤ ((157332971 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12242 * 12242 *
      (1 + BstLean.Part154.deltaChi 12242 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180086637 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12242 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180086637 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12242 : ℝ) / BstLean.Part154.csC) ≤ (97220107 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12242 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97220107 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12242 : ℝ) * (157332971 / 1000000) +
        2 * (1792 / 10000 / 12242) * (180086637 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97220107 / 1000000) *
          (81 / 1000 / 12242 + (1792 / 10000 / 12242) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12242

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12242
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12242 ∧
    1 ≤ gPlus 12242 ∧ gPlus 12242 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12242 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12242 : ℝ) < √(1 - 2 / (12242 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12242 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12242 (gMinus 12242) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12242 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12242 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12242 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12242)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12242 (gMinus 12242) (gPlus 12242)
      (finiteEnergy 12242 12242 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12242 (gMinus 12242) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12242 (gMinus 12242) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12242 (gMinus 12242) (54 / 100))
    (by linarith : energyRatio 12242 (gMinus 12242) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12242 (gMinus 12242) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12242 * kappa (energyRatio 12242 (gMinus 12242) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12242) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12242 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12242 12242 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12242 12242 (11 / 1000) / √12242 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12242)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12242 * kappa (energyRatio 12242 (gMinus 12242) (54 / 100))) +
      2 * √(12 * gPlus 12242) / 12242 + finiteEnergy 12242 12242 (11 / 1000) / √12242 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12242 θ ∧ meanLowerRoot 12242 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12242 - 2 / (12242 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12242 - 2 / (12242 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12242 θ ^ 2 / gPlus 12242) - 2 / (12242 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12242 * (kappa (meanLowerRoot 12242 θ ^ 2 / gPlus 12242) -
        2 / (12242 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12242) / 12242 -
        finiteEnergy 12242 12242 (11 / 1000) / √12242 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12242 θ ^ 2 / gPlus 12242 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12242)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12242 θ ^ 2 / gPlus 12242 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12242)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12242 θ ^ 2 / gPlus 12242 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12242 ^ 2 ≤
      kappa (meanLowerRoot 12242 θ ^ 2 / gPlus 12242) - 2 / (12242 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12242 *
      (kappa (meanLowerRoot 12242 θ ^ 2 / gPlus 12242) - 2 / (12242 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12242 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12242)
    linarith
  have ht : √(12 * gPlus 12242) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12242 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12242 12242 (11 / 1000) / √12242 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12242)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12242 (gMinus 12242) (gPlus 12242)
      (finiteEnergy 12242 12242 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12242) (hτ : 0 < (paperDesignP 12242).tau0 c) :
    eR c = (2 / (mA 12242 : ℝ)) *
      normSq (BstLean.Part150.bT 12242 12242 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12242).tau0 c)) /
      (2 / (12242 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12242).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12242).tau0 c))⁻¹ •
      BstLean.Part150.bT 12242 12242 (A1 c) (A2 c) c.1.2 ((paperDesignP 12242).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12242 : ℝ)) * normSq (bR c) / (2 / (12242 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12242}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12242) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12242).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12242 : ℝ) * (paperDesignP 12242).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12242 12242 c.1.2 ((paperDesignP 12242).tau0 c) :=
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

end BstLean.Part262.Row12242

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12243 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12243).real (BstLean.Part211.CentreSource 12243 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12243) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12243 160 (6 / 1000)
  have hj := jS_160_le (n := 12243) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12243 160 (6 / 1000) ^ 2 * 12243 /
      (((12243 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12243 160 (6 / 1000) ^ 2 * 12243 /
      (((12243 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12243 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12243 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12243) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12243 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12243

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12243) :=
  Ethm (paperCentres 12243) ∩ Ethp (paperCentres 12243)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12243)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12243)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12243) (paperCentres 12243)
  have he : exp (-(45 / 10000 * (12243 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12243 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12243) :=
  (passEvent ∩ agentEv (paperDesignP 12243) (DirectionError 12243) ∩
    agentEv (paperDesignP 12243) (CentreSources 12243 12243)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12243)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12243) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12243) hτ
  have hC := centreSources_ret_charge_row 12243 (paperDesignP 12243) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12243)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12243) (CentreSources 12243 12243)
  direction : analyticBase ⊆ agentEv (paperDesignP 12243) (DirectionError 12243)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12243)) : Set (Ret 12243) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12243)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12243)}
    (hT : (retDist (paperCentres 12243)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12243)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12243)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12243)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12243)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12243)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12243

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12243 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12243 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12243 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12243 12243 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12243)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12243)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12243
  have hb0 := BstLean.Part150.betaJ_nonneg 12243
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12243 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12243 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12243 * BstLean.Part150.betaJ 12243) * 12243) ≤
      (39334849 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12243)) * 12243 := by gcongr <;> linarith
      _ ≤ ((39334849 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12243 * 12243 *
      (1 + BstLean.Part154.deltaChi 12243 12 + 2 / π) / BstLean.Part154.csC) ≤
      (22511749 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12243 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((22511749 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12243 : ℝ) / BstLean.Part154.csC) ≤ (48612039 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12243 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48612039 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12243 : ℝ) * (39334849 / 250000) +
        2 * (1792 / 10000 / 12243) * (22511749 / 125000) +
        4 * (1 / 2.506628) * 1.036505 * (48612039 / 500000) *
          (81 / 1000 / 12243 + (1792 / 10000 / 12243) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12243

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12243
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12243 ∧
    1 ≤ gPlus 12243 ∧ gPlus 12243 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12243 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12243 : ℝ) < √(1 - 2 / (12243 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12243 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12243 (gMinus 12243) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12243 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12243 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12243 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12243)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12243 (gMinus 12243) (gPlus 12243)
      (finiteEnergy 12243 12243 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12243 (gMinus 12243) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12243 (gMinus 12243) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12243 (gMinus 12243) (54 / 100))
    (by linarith : energyRatio 12243 (gMinus 12243) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12243 (gMinus 12243) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12243 * kappa (energyRatio 12243 (gMinus 12243) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12243) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12243 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12243 12243 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12243 12243 (11 / 1000) / √12243 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12243)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12243 * kappa (energyRatio 12243 (gMinus 12243) (54 / 100))) +
      2 * √(12 * gPlus 12243) / 12243 + finiteEnergy 12243 12243 (11 / 1000) / √12243 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12243 θ ∧ meanLowerRoot 12243 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12243 - 2 / (12243 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12243 - 2 / (12243 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12243 θ ^ 2 / gPlus 12243) - 2 / (12243 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12243 * (kappa (meanLowerRoot 12243 θ ^ 2 / gPlus 12243) -
        2 / (12243 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12243) / 12243 -
        finiteEnergy 12243 12243 (11 / 1000) / √12243 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12243 θ ^ 2 / gPlus 12243 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12243)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12243 θ ^ 2 / gPlus 12243 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12243)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12243 θ ^ 2 / gPlus 12243 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12243 ^ 2 ≤
      kappa (meanLowerRoot 12243 θ ^ 2 / gPlus 12243) - 2 / (12243 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12243 *
      (kappa (meanLowerRoot 12243 θ ^ 2 / gPlus 12243) - 2 / (12243 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12243 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12243)
    linarith
  have ht : √(12 * gPlus 12243) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12243 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12243 12243 (11 / 1000) / √12243 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12243)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12243 (gMinus 12243) (gPlus 12243)
      (finiteEnergy 12243 12243 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12243) (hτ : 0 < (paperDesignP 12243).tau0 c) :
    eR c = (2 / (mA 12243 : ℝ)) *
      normSq (BstLean.Part150.bT 12243 12243 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12243).tau0 c)) /
      (2 / (12243 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12243).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12243).tau0 c))⁻¹ •
      BstLean.Part150.bT 12243 12243 (A1 c) (A2 c) c.1.2 ((paperDesignP 12243).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12243 : ℝ)) * normSq (bR c) / (2 / (12243 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12243}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12243) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12243).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12243 : ℝ) * (paperDesignP 12243).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12243 12243 c.1.2 ((paperDesignP 12243).tau0 c) :=
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

end BstLean.Part262.Row12243

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12244 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12244).real (BstLean.Part211.CentreSource 12244 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12244) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12244 160 (6 / 1000)
  have hj := jS_160_le (n := 12244) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12244 160 (6 / 1000) ^ 2 * 12244 /
      (((12244 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12244 160 (6 / 1000) ^ 2 * 12244 /
      (((12244 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12244 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12244 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12244) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12244 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12244

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12244) :=
  Ethm (paperCentres 12244) ∩ Ethp (paperCentres 12244)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12244)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12244)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12244) (paperCentres 12244)
  have he : exp (-(45 / 10000 * (12244 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12244 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12244) :=
  (passEvent ∩ agentEv (paperDesignP 12244) (DirectionError 12244) ∩
    agentEv (paperDesignP 12244) (CentreSources 12244 12244)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12244)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12244) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12244) hτ
  have hC := centreSources_ret_charge_row 12244 (paperDesignP 12244) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12244)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12244) (CentreSources 12244 12244)
  direction : analyticBase ⊆ agentEv (paperDesignP 12244) (DirectionError 12244)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12244)) : Set (Ret 12244) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12244)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12244)}
    (hT : (retDist (paperCentres 12244)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12244)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12244)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12244)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12244)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12244)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12244

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12244 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12244 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12244 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12244 12244 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12244)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12244)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12244
  have hb0 := BstLean.Part150.betaJ_nonneg 12244
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12244 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12244 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12244 * BstLean.Part150.betaJ 12244) * 12244) ≤
      (78672911 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12244)) * 12244 := by gcongr <;> linarith
      _ ≤ ((78672911 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12244 * 12244 *
      (1 + BstLean.Part154.deltaChi 12244 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180101347 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12244 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180101347 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12244 : ℝ) / BstLean.Part154.csC) ≤ (6076753 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12244 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((6076753 / 62500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12244 : ℝ) * (78672911 / 500000) +
        2 * (1792 / 10000 / 12244) * (180101347 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (6076753 / 62500) *
          (81 / 1000 / 12244 + (1792 / 10000 / 12244) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12244

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12244
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12244 ∧
    1 ≤ gPlus 12244 ∧ gPlus 12244 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12244 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12244 : ℝ) < √(1 - 2 / (12244 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12244 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12244 (gMinus 12244) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12244 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12244 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12244 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12244)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12244 (gMinus 12244) (gPlus 12244)
      (finiteEnergy 12244 12244 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12244 (gMinus 12244) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12244 (gMinus 12244) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12244 (gMinus 12244) (54 / 100))
    (by linarith : energyRatio 12244 (gMinus 12244) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12244 (gMinus 12244) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12244 * kappa (energyRatio 12244 (gMinus 12244) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12244) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12244 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12244 12244 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12244 12244 (11 / 1000) / √12244 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12244)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12244 * kappa (energyRatio 12244 (gMinus 12244) (54 / 100))) +
      2 * √(12 * gPlus 12244) / 12244 + finiteEnergy 12244 12244 (11 / 1000) / √12244 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12244 θ ∧ meanLowerRoot 12244 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12244 - 2 / (12244 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12244 - 2 / (12244 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12244 θ ^ 2 / gPlus 12244) - 2 / (12244 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12244 * (kappa (meanLowerRoot 12244 θ ^ 2 / gPlus 12244) -
        2 / (12244 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12244) / 12244 -
        finiteEnergy 12244 12244 (11 / 1000) / √12244 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12244 θ ^ 2 / gPlus 12244 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12244)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12244 θ ^ 2 / gPlus 12244 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12244)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12244 θ ^ 2 / gPlus 12244 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12244 ^ 2 ≤
      kappa (meanLowerRoot 12244 θ ^ 2 / gPlus 12244) - 2 / (12244 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12244 *
      (kappa (meanLowerRoot 12244 θ ^ 2 / gPlus 12244) - 2 / (12244 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12244 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12244)
    linarith
  have ht : √(12 * gPlus 12244) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12244 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12244 12244 (11 / 1000) / √12244 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12244)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12244 (gMinus 12244) (gPlus 12244)
      (finiteEnergy 12244 12244 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12244) (hτ : 0 < (paperDesignP 12244).tau0 c) :
    eR c = (2 / (mA 12244 : ℝ)) *
      normSq (BstLean.Part150.bT 12244 12244 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12244).tau0 c)) /
      (2 / (12244 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12244).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12244).tau0 c))⁻¹ •
      BstLean.Part150.bT 12244 12244 (A1 c) (A2 c) c.1.2 ((paperDesignP 12244).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12244 : ℝ)) * normSq (bR c) / (2 / (12244 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12244}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12244) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12244).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12244 : ℝ) * (paperDesignP 12244).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12244 12244 c.1.2 ((paperDesignP 12244).tau0 c) :=
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

end BstLean.Part262.Row12244

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12245 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12245).real (BstLean.Part211.CentreSource 12245 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12245) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12245 160 (6 / 1000)
  have hj := jS_160_le (n := 12245) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12245 160 (6 / 1000) ^ 2 * 12245 /
      (((12245 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12245 160 (6 / 1000) ^ 2 * 12245 /
      (((12245 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12245 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12245 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12245) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12245 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12245

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12245) :=
  Ethm (paperCentres 12245) ∩ Ethp (paperCentres 12245)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12245)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12245)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12245) (paperCentres 12245)
  have he : exp (-(45 / 10000 * (12245 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12245 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12245) :=
  (passEvent ∩ agentEv (paperDesignP 12245) (DirectionError 12245) ∩
    agentEv (paperDesignP 12245) (CentreSources 12245 12245)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12245)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12245) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12245) hτ
  have hC := centreSources_ret_charge_row 12245 (paperDesignP 12245) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12245)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12245) (CentreSources 12245 12245)
  direction : analyticBase ⊆ agentEv (paperDesignP 12245) (DirectionError 12245)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12245)) : Set (Ret 12245) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12245)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12245)}
    (hT : (retDist (paperCentres 12245)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12245)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12245)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12245)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12245)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12245)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12245

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12245 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12245 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12245 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12245 12245 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12245)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12245)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12245
  have hb0 := BstLean.Part150.betaJ_nonneg 12245
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12245 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12245 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12245 * BstLean.Part150.betaJ 12245) * 12245) ≤
      (157352247 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12245)) * 12245 := by gcongr <;> linarith
      _ ≤ ((157352247 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12245 * 12245 *
      (1 + BstLean.Part154.deltaChi 12245 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90054351 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12245 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90054351 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12245 : ℝ) / BstLean.Part154.csC) ≤ (97232019 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12245 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97232019 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12245 : ℝ) * (157352247 / 1000000) +
        2 * (1792 / 10000 / 12245) * (90054351 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (97232019 / 1000000) *
          (81 / 1000 / 12245 + (1792 / 10000 / 12245) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12245

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12245
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12245 ∧
    1 ≤ gPlus 12245 ∧ gPlus 12245 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12245 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12245 : ℝ) < √(1 - 2 / (12245 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12245 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12245 (gMinus 12245) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12245 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12245 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12245 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12245)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12245 (gMinus 12245) (gPlus 12245)
      (finiteEnergy 12245 12245 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12245 (gMinus 12245) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12245 (gMinus 12245) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12245 (gMinus 12245) (54 / 100))
    (by linarith : energyRatio 12245 (gMinus 12245) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12245 (gMinus 12245) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12245 * kappa (energyRatio 12245 (gMinus 12245) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12245) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12245 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12245 12245 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12245 12245 (11 / 1000) / √12245 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12245)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12245 * kappa (energyRatio 12245 (gMinus 12245) (54 / 100))) +
      2 * √(12 * gPlus 12245) / 12245 + finiteEnergy 12245 12245 (11 / 1000) / √12245 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12245 θ ∧ meanLowerRoot 12245 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12245 - 2 / (12245 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12245 - 2 / (12245 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12245 θ ^ 2 / gPlus 12245) - 2 / (12245 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12245 * (kappa (meanLowerRoot 12245 θ ^ 2 / gPlus 12245) -
        2 / (12245 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12245) / 12245 -
        finiteEnergy 12245 12245 (11 / 1000) / √12245 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12245 θ ^ 2 / gPlus 12245 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12245)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12245 θ ^ 2 / gPlus 12245 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12245)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12245 θ ^ 2 / gPlus 12245 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12245 ^ 2 ≤
      kappa (meanLowerRoot 12245 θ ^ 2 / gPlus 12245) - 2 / (12245 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12245 *
      (kappa (meanLowerRoot 12245 θ ^ 2 / gPlus 12245) - 2 / (12245 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12245 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12245)
    linarith
  have ht : √(12 * gPlus 12245) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12245 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12245 12245 (11 / 1000) / √12245 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12245)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12245 (gMinus 12245) (gPlus 12245)
      (finiteEnergy 12245 12245 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12245) (hτ : 0 < (paperDesignP 12245).tau0 c) :
    eR c = (2 / (mA 12245 : ℝ)) *
      normSq (BstLean.Part150.bT 12245 12245 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12245).tau0 c)) /
      (2 / (12245 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12245).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12245).tau0 c))⁻¹ •
      BstLean.Part150.bT 12245 12245 (A1 c) (A2 c) c.1.2 ((paperDesignP 12245).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12245 : ℝ)) * normSq (bR c) / (2 / (12245 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12245}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12245) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12245).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12245 : ℝ) * (paperDesignP 12245).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12245 12245 c.1.2 ((paperDesignP 12245).tau0 c) :=
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

end BstLean.Part262.Row12245

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12246 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12246).real (BstLean.Part211.CentreSource 12246 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12246) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12246 160 (6 / 1000)
  have hj := jS_160_le (n := 12246) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12246 160 (6 / 1000) ^ 2 * 12246 /
      (((12246 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12246 160 (6 / 1000) ^ 2 * 12246 /
      (((12246 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12246 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12246 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12246) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12246 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12246

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12246) :=
  Ethm (paperCentres 12246) ∩ Ethp (paperCentres 12246)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12246)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12246)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12246) (paperCentres 12246)
  have he : exp (-(45 / 10000 * (12246 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12246 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12246) :=
  (passEvent ∩ agentEv (paperDesignP 12246) (DirectionError 12246) ∩
    agentEv (paperDesignP 12246) (CentreSources 12246 12246)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12246)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12246) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12246) hτ
  have hC := centreSources_ret_charge_row 12246 (paperDesignP 12246) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12246)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12246) (CentreSources 12246 12246)
  direction : analyticBase ⊆ agentEv (paperDesignP 12246) (DirectionError 12246)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12246)) : Set (Ret 12246) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12246)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12246)}
    (hT : (retDist (paperCentres 12246)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12246)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12246)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12246)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12246)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12246)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12246

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12246 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12246 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12246 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12246 12246 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12246)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12246)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12246
  have hb0 := BstLean.Part150.betaJ_nonneg 12246
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12246 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12246 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12246 * BstLean.Part150.betaJ 12246) * 12246) ≤
      (9834917 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12246)) * 12246 := by gcongr <;> linarith
      _ ≤ ((9834917 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12246 * 12246 *
      (1 + BstLean.Part154.deltaChi 12246 12 + 2 / π) / BstLean.Part154.csC) ≤
      (22514507 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12246 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((22514507 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12246 : ℝ) / BstLean.Part154.csC) ≤ (97235989 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12246 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97235989 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12246 : ℝ) * (9834917 / 62500) +
        2 * (1792 / 10000 / 12246) * (22514507 / 125000) +
        4 * (1 / 2.506628) * 1.036505 * (97235989 / 1000000) *
          (81 / 1000 / 12246 + (1792 / 10000 / 12246) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12246

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12246
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12246 ∧
    1 ≤ gPlus 12246 ∧ gPlus 12246 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12246 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12246 : ℝ) < √(1 - 2 / (12246 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12246 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12246 (gMinus 12246) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12246 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12246 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12246 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12246)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12246 (gMinus 12246) (gPlus 12246)
      (finiteEnergy 12246 12246 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12246 (gMinus 12246) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12246 (gMinus 12246) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12246 (gMinus 12246) (54 / 100))
    (by linarith : energyRatio 12246 (gMinus 12246) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12246 (gMinus 12246) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12246 * kappa (energyRatio 12246 (gMinus 12246) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12246) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12246 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12246 12246 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12246 12246 (11 / 1000) / √12246 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12246)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12246 * kappa (energyRatio 12246 (gMinus 12246) (54 / 100))) +
      2 * √(12 * gPlus 12246) / 12246 + finiteEnergy 12246 12246 (11 / 1000) / √12246 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12246 θ ∧ meanLowerRoot 12246 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12246 - 2 / (12246 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12246 - 2 / (12246 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12246 θ ^ 2 / gPlus 12246) - 2 / (12246 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12246 * (kappa (meanLowerRoot 12246 θ ^ 2 / gPlus 12246) -
        2 / (12246 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12246) / 12246 -
        finiteEnergy 12246 12246 (11 / 1000) / √12246 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12246 θ ^ 2 / gPlus 12246 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12246)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12246 θ ^ 2 / gPlus 12246 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12246)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12246 θ ^ 2 / gPlus 12246 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12246 ^ 2 ≤
      kappa (meanLowerRoot 12246 θ ^ 2 / gPlus 12246) - 2 / (12246 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12246 *
      (kappa (meanLowerRoot 12246 θ ^ 2 / gPlus 12246) - 2 / (12246 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12246 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12246)
    linarith
  have ht : √(12 * gPlus 12246) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12246 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12246 12246 (11 / 1000) / √12246 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12246)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12246 (gMinus 12246) (gPlus 12246)
      (finiteEnergy 12246 12246 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12246) (hτ : 0 < (paperDesignP 12246).tau0 c) :
    eR c = (2 / (mA 12246 : ℝ)) *
      normSq (BstLean.Part150.bT 12246 12246 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12246).tau0 c)) /
      (2 / (12246 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12246).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12246).tau0 c))⁻¹ •
      BstLean.Part150.bT 12246 12246 (A1 c) (A2 c) c.1.2 ((paperDesignP 12246).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12246 : ℝ)) * normSq (bR c) / (2 / (12246 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12246}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12246) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12246).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12246 : ℝ) * (paperDesignP 12246).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12246 12246 c.1.2 ((paperDesignP 12246).tau0 c) :=
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

end BstLean.Part262.Row12246

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12247 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12247).real (BstLean.Part211.CentreSource 12247 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12247) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12247 160 (6 / 1000)
  have hj := jS_160_le (n := 12247) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12247 160 (6 / 1000) ^ 2 * 12247 /
      (((12247 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12247 160 (6 / 1000) ^ 2 * 12247 /
      (((12247 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12247 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12247 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12247) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12247 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12247

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12247) :=
  Ethm (paperCentres 12247) ∩ Ethp (paperCentres 12247)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12247)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12247)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12247) (paperCentres 12247)
  have he : exp (-(45 / 10000 * (12247 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12247 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12247) :=
  (passEvent ∩ agentEv (paperDesignP 12247) (DirectionError 12247) ∩
    agentEv (paperDesignP 12247) (CentreSources 12247 12247)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12247)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12247) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12247) hτ
  have hC := centreSources_ret_charge_row 12247 (paperDesignP 12247) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12247)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12247) (CentreSources 12247 12247)
  direction : analyticBase ⊆ agentEv (paperDesignP 12247) (DirectionError 12247)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12247)) : Set (Ret 12247) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12247)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12247)}
    (hT : (retDist (paperCentres 12247)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12247)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12247)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12247)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12247)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12247)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12247

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12247 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12247 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12247 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12247 12247 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12247)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12247)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12247
  have hb0 := BstLean.Part150.betaJ_nonneg 12247
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12247 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12247 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12247 * BstLean.Part150.betaJ 12247) * 12247) ≤
      (157365097 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12247)) * 12247 := by gcongr <;> linarith
      _ ≤ ((157365097 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12247 * 12247 *
      (1 + BstLean.Part154.deltaChi 12247 12 + 2 / π) / BstLean.Part154.csC) ≤
      (18012341 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12247 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((18012341 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12247 : ℝ) / BstLean.Part154.csC) ≤ (97239959 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12247 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97239959 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12247 : ℝ) * (157365097 / 1000000) +
        2 * (1792 / 10000 / 12247) * (18012341 / 100000) +
        4 * (1 / 2.506628) * 1.036505 * (97239959 / 1000000) *
          (81 / 1000 / 12247 + (1792 / 10000 / 12247) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12247

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12247
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12247 ∧
    1 ≤ gPlus 12247 ∧ gPlus 12247 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12247 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12247 : ℝ) < √(1 - 2 / (12247 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12247 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12247 (gMinus 12247) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12247 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12247 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12247 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12247)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12247 (gMinus 12247) (gPlus 12247)
      (finiteEnergy 12247 12247 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12247 (gMinus 12247) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12247 (gMinus 12247) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12247 (gMinus 12247) (54 / 100))
    (by linarith : energyRatio 12247 (gMinus 12247) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12247 (gMinus 12247) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12247 * kappa (energyRatio 12247 (gMinus 12247) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12247) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12247 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12247 12247 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12247 12247 (11 / 1000) / √12247 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12247)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12247 * kappa (energyRatio 12247 (gMinus 12247) (54 / 100))) +
      2 * √(12 * gPlus 12247) / 12247 + finiteEnergy 12247 12247 (11 / 1000) / √12247 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12247 θ ∧ meanLowerRoot 12247 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12247 - 2 / (12247 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12247 - 2 / (12247 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12247 θ ^ 2 / gPlus 12247) - 2 / (12247 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12247 * (kappa (meanLowerRoot 12247 θ ^ 2 / gPlus 12247) -
        2 / (12247 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12247) / 12247 -
        finiteEnergy 12247 12247 (11 / 1000) / √12247 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12247 θ ^ 2 / gPlus 12247 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12247)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12247 θ ^ 2 / gPlus 12247 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12247)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12247 θ ^ 2 / gPlus 12247 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12247 ^ 2 ≤
      kappa (meanLowerRoot 12247 θ ^ 2 / gPlus 12247) - 2 / (12247 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12247 *
      (kappa (meanLowerRoot 12247 θ ^ 2 / gPlus 12247) - 2 / (12247 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12247 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12247)
    linarith
  have ht : √(12 * gPlus 12247) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12247 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12247 12247 (11 / 1000) / √12247 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12247)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12247 (gMinus 12247) (gPlus 12247)
      (finiteEnergy 12247 12247 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12247) (hτ : 0 < (paperDesignP 12247).tau0 c) :
    eR c = (2 / (mA 12247 : ℝ)) *
      normSq (BstLean.Part150.bT 12247 12247 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12247).tau0 c)) /
      (2 / (12247 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12247).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12247).tau0 c))⁻¹ •
      BstLean.Part150.bT 12247 12247 (A1 c) (A2 c) c.1.2 ((paperDesignP 12247).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12247 : ℝ)) * normSq (bR c) / (2 / (12247 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12247}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12247) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12247).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12247 : ℝ) * (paperDesignP 12247).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12247 12247 c.1.2 ((paperDesignP 12247).tau0 c) :=
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

end BstLean.Part262.Row12247

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12248 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12248).real (BstLean.Part211.CentreSource 12248 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12248) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12248 160 (6 / 1000)
  have hj := jS_160_le (n := 12248) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12248 160 (6 / 1000) ^ 2 * 12248 /
      (((12248 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12248 160 (6 / 1000) ^ 2 * 12248 /
      (((12248 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12248 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12248 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12248) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12248 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12248

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12248) :=
  Ethm (paperCentres 12248) ∩ Ethp (paperCentres 12248)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12248)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12248)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12248) (paperCentres 12248)
  have he : exp (-(45 / 10000 * (12248 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12248 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12248) :=
  (passEvent ∩ agentEv (paperDesignP 12248) (DirectionError 12248) ∩
    agentEv (paperDesignP 12248) (CentreSources 12248 12248)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12248)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12248) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12248) hτ
  have hC := centreSources_ret_charge_row 12248 (paperDesignP 12248) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12248)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12248) (CentreSources 12248 12248)
  direction : analyticBase ⊆ agentEv (paperDesignP 12248) (DirectionError 12248)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12248)) : Set (Ret 12248) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12248)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12248)}
    (hT : (retDist (paperCentres 12248)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12248)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12248)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12248)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12248)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12248)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12248

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12248 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12248 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12248 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12248 12248 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12248)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12248)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12248
  have hb0 := BstLean.Part150.betaJ_nonneg 12248
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12248 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12248 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12248 * BstLean.Part150.betaJ 12248) * 12248) ≤
      (157371521 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12248)) * 12248 := by gcongr <;> linarith
      _ ≤ ((157371521 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12248 * 12248 *
      (1 + BstLean.Part154.deltaChi 12248 12 + 2 / π) / BstLean.Part154.csC) ≤
      (45032691 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12248 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((45032691 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12248 : ℝ) / BstLean.Part154.csC) ≤ (97243929 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12248 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97243929 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12248 : ℝ) * (157371521 / 1000000) +
        2 * (1792 / 10000 / 12248) * (45032691 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (97243929 / 1000000) *
          (81 / 1000 / 12248 + (1792 / 10000 / 12248) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12248

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12248
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12248 ∧
    1 ≤ gPlus 12248 ∧ gPlus 12248 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12248 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12248 : ℝ) < √(1 - 2 / (12248 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12248 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12248 (gMinus 12248) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12248 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12248 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12248 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12248)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12248 (gMinus 12248) (gPlus 12248)
      (finiteEnergy 12248 12248 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12248 (gMinus 12248) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12248 (gMinus 12248) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12248 (gMinus 12248) (54 / 100))
    (by linarith : energyRatio 12248 (gMinus 12248) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12248 (gMinus 12248) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12248 * kappa (energyRatio 12248 (gMinus 12248) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12248) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12248 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12248 12248 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12248 12248 (11 / 1000) / √12248 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12248)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12248 * kappa (energyRatio 12248 (gMinus 12248) (54 / 100))) +
      2 * √(12 * gPlus 12248) / 12248 + finiteEnergy 12248 12248 (11 / 1000) / √12248 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12248 θ ∧ meanLowerRoot 12248 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12248 - 2 / (12248 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12248 - 2 / (12248 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12248 θ ^ 2 / gPlus 12248) - 2 / (12248 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12248 * (kappa (meanLowerRoot 12248 θ ^ 2 / gPlus 12248) -
        2 / (12248 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12248) / 12248 -
        finiteEnergy 12248 12248 (11 / 1000) / √12248 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12248 θ ^ 2 / gPlus 12248 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12248)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12248 θ ^ 2 / gPlus 12248 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12248)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12248 θ ^ 2 / gPlus 12248 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12248 ^ 2 ≤
      kappa (meanLowerRoot 12248 θ ^ 2 / gPlus 12248) - 2 / (12248 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12248 *
      (kappa (meanLowerRoot 12248 θ ^ 2 / gPlus 12248) - 2 / (12248 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12248 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12248)
    linarith
  have ht : √(12 * gPlus 12248) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12248 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12248 12248 (11 / 1000) / √12248 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12248)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12248 (gMinus 12248) (gPlus 12248)
      (finiteEnergy 12248 12248 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12248) (hτ : 0 < (paperDesignP 12248).tau0 c) :
    eR c = (2 / (mA 12248 : ℝ)) *
      normSq (BstLean.Part150.bT 12248 12248 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12248).tau0 c)) /
      (2 / (12248 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12248).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12248).tau0 c))⁻¹ •
      BstLean.Part150.bT 12248 12248 (A1 c) (A2 c) c.1.2 ((paperDesignP 12248).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12248 : ℝ)) * normSq (bR c) / (2 / (12248 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12248}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12248) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12248).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12248 : ℝ) * (paperDesignP 12248).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12248 12248 c.1.2 ((paperDesignP 12248).tau0 c) :=
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

end BstLean.Part262.Row12248

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12249 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12249).real (BstLean.Part211.CentreSource 12249 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12249) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12249 160 (6 / 1000)
  have hj := jS_160_le (n := 12249) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12249 160 (6 / 1000) ^ 2 * 12249 /
      (((12249 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12249 160 (6 / 1000) ^ 2 * 12249 /
      (((12249 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12249 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12249 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12249) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12249 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12249

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12249) :=
  Ethm (paperCentres 12249) ∩ Ethp (paperCentres 12249)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12249)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12249)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12249) (paperCentres 12249)
  have he : exp (-(45 / 10000 * (12249 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12249 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12249) :=
  (passEvent ∩ agentEv (paperDesignP 12249) (DirectionError 12249) ∩
    agentEv (paperDesignP 12249) (CentreSources 12249 12249)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12249)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12249) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12249) hτ
  have hC := centreSources_ret_charge_row 12249 (paperDesignP 12249) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12249)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12249) (CentreSources 12249 12249)
  direction : analyticBase ⊆ agentEv (paperDesignP 12249) (DirectionError 12249)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12249)) : Set (Ret 12249) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12249)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12249)}
    (hT : (retDist (paperCentres 12249)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12249)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12249)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12249)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12249)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12249)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12249

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12249 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12249 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12249 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12249 12249 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12249)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12249)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12249
  have hb0 := BstLean.Part150.betaJ_nonneg 12249
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12249 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12249 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12249 * BstLean.Part150.betaJ 12249) * 12249) ≤
      (31475589 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12249)) * 12249 := by gcongr <;> linarith
      _ ≤ ((31475589 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12249 * 12249 *
      (1 + BstLean.Part154.deltaChi 12249 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180138117 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12249 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180138117 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12249 : ℝ) / BstLean.Part154.csC) ≤ (97247899 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12249 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97247899 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12249 : ℝ) * (31475589 / 200000) +
        2 * (1792 / 10000 / 12249) * (180138117 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97247899 / 1000000) *
          (81 / 1000 / 12249 + (1792 / 10000 / 12249) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12249

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12249
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12249 ∧
    1 ≤ gPlus 12249 ∧ gPlus 12249 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12249 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12249 : ℝ) < √(1 - 2 / (12249 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12249 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12249 (gMinus 12249) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12249 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12249 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12249 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12249)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12249 (gMinus 12249) (gPlus 12249)
      (finiteEnergy 12249 12249 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12249 (gMinus 12249) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12249 (gMinus 12249) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12249 (gMinus 12249) (54 / 100))
    (by linarith : energyRatio 12249 (gMinus 12249) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12249 (gMinus 12249) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12249 * kappa (energyRatio 12249 (gMinus 12249) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12249) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12249 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12249 12249 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12249 12249 (11 / 1000) / √12249 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12249)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12249 * kappa (energyRatio 12249 (gMinus 12249) (54 / 100))) +
      2 * √(12 * gPlus 12249) / 12249 + finiteEnergy 12249 12249 (11 / 1000) / √12249 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12249 θ ∧ meanLowerRoot 12249 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12249 - 2 / (12249 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12249 - 2 / (12249 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12249 θ ^ 2 / gPlus 12249) - 2 / (12249 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12249 * (kappa (meanLowerRoot 12249 θ ^ 2 / gPlus 12249) -
        2 / (12249 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12249) / 12249 -
        finiteEnergy 12249 12249 (11 / 1000) / √12249 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12249 θ ^ 2 / gPlus 12249 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12249)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12249 θ ^ 2 / gPlus 12249 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12249)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12249 θ ^ 2 / gPlus 12249 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12249 ^ 2 ≤
      kappa (meanLowerRoot 12249 θ ^ 2 / gPlus 12249) - 2 / (12249 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12249 *
      (kappa (meanLowerRoot 12249 θ ^ 2 / gPlus 12249) - 2 / (12249 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12249 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12249)
    linarith
  have ht : √(12 * gPlus 12249) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12249 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12249 12249 (11 / 1000) / √12249 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12249)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12249 (gMinus 12249) (gPlus 12249)
      (finiteEnergy 12249 12249 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12249) (hτ : 0 < (paperDesignP 12249).tau0 c) :
    eR c = (2 / (mA 12249 : ℝ)) *
      normSq (BstLean.Part150.bT 12249 12249 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12249).tau0 c)) /
      (2 / (12249 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12249).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12249).tau0 c))⁻¹ •
      BstLean.Part150.bT 12249 12249 (A1 c) (A2 c) c.1.2 ((paperDesignP 12249).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12249 : ℝ)) * normSq (bR c) / (2 / (12249 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12249}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12249) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12249).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12249 : ℝ) * (paperDesignP 12249).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12249 12249 c.1.2 ((paperDesignP 12249).tau0 c) :=
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

end BstLean.Part262.Row12249
