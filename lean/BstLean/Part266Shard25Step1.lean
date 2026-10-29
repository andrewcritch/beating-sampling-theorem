import BstLean.Part266Shard25Step0


/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12975 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12975).real (BstLean.Part211.CentreSource 12975 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12975) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12975 160 (6 / 1000)
  have hj := jS_160_le (n := 12975) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12975 160 (6 / 1000) ^ 2 * 12975 /
      (((12975 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12975 160 (6 / 1000) ^ 2 * 12975 /
      (((12975 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12975 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12975 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12975) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12975 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12975

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12975) :=
  Ethm (paperCentres 12975) ∩ Ethp (paperCentres 12975)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12975)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12975)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12975) (paperCentres 12975)
  have he : exp (-(45 / 10000 * (12975 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12975 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12975) :=
  (passEvent ∩ agentEv (paperDesignP 12975) (DirectionError 12975) ∩
    agentEv (paperDesignP 12975) (CentreSources 12975 12975)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12975)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12975) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12975) hτ
  have hC := centreSources_ret_charge_row 12975 (paperDesignP 12975) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12975)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12975) (CentreSources 12975 12975)
  direction : analyticBase ⊆ agentEv (paperDesignP 12975) (DirectionError 12975)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12975)) : Set (Ret 12975) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12975)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12975)}
    (hT : (retDist (paperCentres 12975)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12975)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12975)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12975)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12975)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12975)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12975

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12975 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12975 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12975 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12975 12975 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12975)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12975)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12975
  have hb0 := BstLean.Part150.betaJ_nonneg 12975
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12975 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12975 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12975 * BstLean.Part150.betaJ 12975) * 12975) ≤
      (80987329 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12975)) * 12975 := by gcongr <;> linarith
      _ ≤ ((80987329 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12975 * 12975 *
      (1 + BstLean.Part154.deltaChi 12975 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92699841 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12975 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92699841 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12975 : ℝ) / BstLean.Part154.csC) ≤ (25022091 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12975 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((25022091 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12975 : ℝ) * (80987329 / 500000) +
        2 * (1792 / 10000 / 12975) * (92699841 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (25022091 / 250000) *
          (81 / 1000 / 12975 + (1792 / 10000 / 12975) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12975

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12975
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12975 ∧
    1 ≤ gPlus 12975 ∧ gPlus 12975 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12975 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12975 : ℝ) < √(1 - 2 / (12975 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12975 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12975 (gMinus 12975) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12975 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12975 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12975 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12975)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12975 (gMinus 12975) (gPlus 12975)
      (finiteEnergy 12975 12975 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12975 (gMinus 12975) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12975 (gMinus 12975) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12975 (gMinus 12975) (54 / 100))
    (by linarith : energyRatio 12975 (gMinus 12975) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12975 (gMinus 12975) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12975 * kappa (energyRatio 12975 (gMinus 12975) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12975) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12975 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12975 12975 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12975 12975 (11 / 1000) / √12975 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12975)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12975 * kappa (energyRatio 12975 (gMinus 12975) (54 / 100))) +
      2 * √(12 * gPlus 12975) / 12975 + finiteEnergy 12975 12975 (11 / 1000) / √12975 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12975 θ ∧ meanLowerRoot 12975 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12975 - 2 / (12975 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12975 - 2 / (12975 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12975 θ ^ 2 / gPlus 12975) - 2 / (12975 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12975 * (kappa (meanLowerRoot 12975 θ ^ 2 / gPlus 12975) -
        2 / (12975 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12975) / 12975 -
        finiteEnergy 12975 12975 (11 / 1000) / √12975 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12975 θ ^ 2 / gPlus 12975 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12975)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12975 θ ^ 2 / gPlus 12975 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12975)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12975 θ ^ 2 / gPlus 12975 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12975 ^ 2 ≤
      kappa (meanLowerRoot 12975 θ ^ 2 / gPlus 12975) - 2 / (12975 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12975 *
      (kappa (meanLowerRoot 12975 θ ^ 2 / gPlus 12975) - 2 / (12975 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12975 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12975)
    linarith
  have ht : √(12 * gPlus 12975) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12975 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12975 12975 (11 / 1000) / √12975 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12975)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12975 (gMinus 12975) (gPlus 12975)
      (finiteEnergy 12975 12975 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12975) (hτ : 0 < (paperDesignP 12975).tau0 c) :
    eR c = (2 / (mA 12975 : ℝ)) *
      normSq (BstLean.Part150.bT 12975 12975 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12975).tau0 c)) /
      (2 / (12975 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12975).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12975).tau0 c))⁻¹ •
      BstLean.Part150.bT 12975 12975 (A1 c) (A2 c) c.1.2 ((paperDesignP 12975).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12975 : ℝ)) * normSq (bR c) / (2 / (12975 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12975}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12975) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12975).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12975 : ℝ) * (paperDesignP 12975).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12975 12975 c.1.2 ((paperDesignP 12975).tau0 c) :=
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

end BstLean.Part266.Row12975

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12976 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12976).real (BstLean.Part211.CentreSource 12976 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12976) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12976 160 (6 / 1000)
  have hj := jS_160_le (n := 12976) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12976 160 (6 / 1000) ^ 2 * 12976 /
      (((12976 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12976 160 (6 / 1000) ^ 2 * 12976 /
      (((12976 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12976 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12976 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12976) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12976 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12976

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12976) :=
  Ethm (paperCentres 12976) ∩ Ethp (paperCentres 12976)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12976)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12976)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12976) (paperCentres 12976)
  have he : exp (-(45 / 10000 * (12976 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12976 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12976) :=
  (passEvent ∩ agentEv (paperDesignP 12976) (DirectionError 12976) ∩
    agentEv (paperDesignP 12976) (CentreSources 12976 12976)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12976)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12976) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12976) hτ
  have hC := centreSources_ret_charge_row 12976 (paperDesignP 12976) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12976)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12976) (CentreSources 12976 12976)
  direction : analyticBase ⊆ agentEv (paperDesignP 12976) (DirectionError 12976)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12976)) : Set (Ret 12976) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12976)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12976)}
    (hT : (retDist (paperCentres 12976)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12976)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12976)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12976)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12976)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12976)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12976

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12976 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12976 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12976 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12976 12976 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12976)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12976)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12976
  have hb0 := BstLean.Part150.betaJ_nonneg 12976
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12976 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12976 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12976 * BstLean.Part150.betaJ 12976) * 12976) ≤
      (161980899 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12976)) * 12976 := by gcongr <;> linarith
      _ ≤ ((161980899 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12976 * 12976 *
      (1 + BstLean.Part154.deltaChi 12976 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92703413 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12976 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92703413 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12976 : ℝ) / BstLean.Part154.csC) ≤ (100092221 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12976 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100092221 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12976 : ℝ) * (161980899 / 1000000) +
        2 * (1792 / 10000 / 12976) * (92703413 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100092221 / 1000000) *
          (81 / 1000 / 12976 + (1792 / 10000 / 12976) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12976

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12976
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12976 ∧
    1 ≤ gPlus 12976 ∧ gPlus 12976 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12976 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12976 : ℝ) < √(1 - 2 / (12976 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12976 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12976 (gMinus 12976) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12976 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12976 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12976 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12976)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12976 (gMinus 12976) (gPlus 12976)
      (finiteEnergy 12976 12976 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12976 (gMinus 12976) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12976 (gMinus 12976) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12976 (gMinus 12976) (54 / 100))
    (by linarith : energyRatio 12976 (gMinus 12976) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12976 (gMinus 12976) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12976 * kappa (energyRatio 12976 (gMinus 12976) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12976) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12976 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12976 12976 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12976 12976 (11 / 1000) / √12976 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12976)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12976 * kappa (energyRatio 12976 (gMinus 12976) (54 / 100))) +
      2 * √(12 * gPlus 12976) / 12976 + finiteEnergy 12976 12976 (11 / 1000) / √12976 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12976 θ ∧ meanLowerRoot 12976 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12976 - 2 / (12976 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12976 - 2 / (12976 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12976 θ ^ 2 / gPlus 12976) - 2 / (12976 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12976 * (kappa (meanLowerRoot 12976 θ ^ 2 / gPlus 12976) -
        2 / (12976 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12976) / 12976 -
        finiteEnergy 12976 12976 (11 / 1000) / √12976 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12976 θ ^ 2 / gPlus 12976 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12976)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12976 θ ^ 2 / gPlus 12976 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12976)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12976 θ ^ 2 / gPlus 12976 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12976 ^ 2 ≤
      kappa (meanLowerRoot 12976 θ ^ 2 / gPlus 12976) - 2 / (12976 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12976 *
      (kappa (meanLowerRoot 12976 θ ^ 2 / gPlus 12976) - 2 / (12976 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12976 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12976)
    linarith
  have ht : √(12 * gPlus 12976) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12976 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12976 12976 (11 / 1000) / √12976 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12976)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12976 (gMinus 12976) (gPlus 12976)
      (finiteEnergy 12976 12976 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12976) (hτ : 0 < (paperDesignP 12976).tau0 c) :
    eR c = (2 / (mA 12976 : ℝ)) *
      normSq (BstLean.Part150.bT 12976 12976 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12976).tau0 c)) /
      (2 / (12976 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12976).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12976).tau0 c))⁻¹ •
      BstLean.Part150.bT 12976 12976 (A1 c) (A2 c) c.1.2 ((paperDesignP 12976).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12976 : ℝ)) * normSq (bR c) / (2 / (12976 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12976}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12976) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12976).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12976 : ℝ) * (paperDesignP 12976).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12976 12976 c.1.2 ((paperDesignP 12976).tau0 c) :=
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

end BstLean.Part266.Row12976

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12977 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12977).real (BstLean.Part211.CentreSource 12977 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12977) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12977 160 (6 / 1000)
  have hj := jS_160_le (n := 12977) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12977 160 (6 / 1000) ^ 2 * 12977 /
      (((12977 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12977 160 (6 / 1000) ^ 2 * 12977 /
      (((12977 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12977 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12977 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12977) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12977 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12977

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12977) :=
  Ethm (paperCentres 12977) ∩ Ethp (paperCentres 12977)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12977)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12977)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12977) (paperCentres 12977)
  have he : exp (-(45 / 10000 * (12977 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12977 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12977) :=
  (passEvent ∩ agentEv (paperDesignP 12977) (DirectionError 12977) ∩
    agentEv (paperDesignP 12977) (CentreSources 12977 12977)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12977)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12977) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12977) hτ
  have hC := centreSources_ret_charge_row 12977 (paperDesignP 12977) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12977)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12977) (CentreSources 12977 12977)
  direction : analyticBase ⊆ agentEv (paperDesignP 12977) (DirectionError 12977)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12977)) : Set (Ret 12977) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12977)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12977)}
    (hT : (retDist (paperCentres 12977)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12977)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12977)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12977)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12977)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12977)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12977

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12977 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12977 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12977 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12977 12977 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12977)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12977)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12977
  have hb0 := BstLean.Part150.betaJ_nonneg 12977
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12977 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12977 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12977 * BstLean.Part150.betaJ 12977) * 12977) ≤
      (8099357 / 50000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12977)) * 12977 := by gcongr <;> linarith
      _ ≤ ((8099357 / 50000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12977 * 12977 *
      (1 + BstLean.Part154.deltaChi 12977 12 + 2 / π) / BstLean.Part154.csC) ≤
      (18541397 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12977 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((18541397 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12977 : ℝ) / BstLean.Part154.csC) ≤ (50048039 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12977 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50048039 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12977 : ℝ) * (8099357 / 50000) +
        2 * (1792 / 10000 / 12977) * (18541397 / 100000) +
        4 * (1 / 2.506628) * 1.036505 * (50048039 / 500000) *
          (81 / 1000 / 12977 + (1792 / 10000 / 12977) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12977

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12977
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12977 ∧
    1 ≤ gPlus 12977 ∧ gPlus 12977 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12977 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12977 : ℝ) < √(1 - 2 / (12977 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12977 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12977 (gMinus 12977) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12977 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12977 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12977 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12977)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12977 (gMinus 12977) (gPlus 12977)
      (finiteEnergy 12977 12977 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12977 (gMinus 12977) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12977 (gMinus 12977) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12977 (gMinus 12977) (54 / 100))
    (by linarith : energyRatio 12977 (gMinus 12977) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12977 (gMinus 12977) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12977 * kappa (energyRatio 12977 (gMinus 12977) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12977) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12977 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12977 12977 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12977 12977 (11 / 1000) / √12977 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12977)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12977 * kappa (energyRatio 12977 (gMinus 12977) (54 / 100))) +
      2 * √(12 * gPlus 12977) / 12977 + finiteEnergy 12977 12977 (11 / 1000) / √12977 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12977 θ ∧ meanLowerRoot 12977 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12977 - 2 / (12977 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12977 - 2 / (12977 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12977 θ ^ 2 / gPlus 12977) - 2 / (12977 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12977 * (kappa (meanLowerRoot 12977 θ ^ 2 / gPlus 12977) -
        2 / (12977 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12977) / 12977 -
        finiteEnergy 12977 12977 (11 / 1000) / √12977 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12977 θ ^ 2 / gPlus 12977 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12977)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12977 θ ^ 2 / gPlus 12977 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12977)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12977 θ ^ 2 / gPlus 12977 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12977 ^ 2 ≤
      kappa (meanLowerRoot 12977 θ ^ 2 / gPlus 12977) - 2 / (12977 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12977 *
      (kappa (meanLowerRoot 12977 θ ^ 2 / gPlus 12977) - 2 / (12977 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12977 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12977)
    linarith
  have ht : √(12 * gPlus 12977) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12977 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12977 12977 (11 / 1000) / √12977 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12977)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12977 (gMinus 12977) (gPlus 12977)
      (finiteEnergy 12977 12977 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12977) (hτ : 0 < (paperDesignP 12977).tau0 c) :
    eR c = (2 / (mA 12977 : ℝ)) *
      normSq (BstLean.Part150.bT 12977 12977 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12977).tau0 c)) /
      (2 / (12977 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12977).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12977).tau0 c))⁻¹ •
      BstLean.Part150.bT 12977 12977 (A1 c) (A2 c) c.1.2 ((paperDesignP 12977).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12977 : ℝ)) * normSq (bR c) / (2 / (12977 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12977}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12977) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12977).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12977 : ℝ) * (paperDesignP 12977).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12977 12977 c.1.2 ((paperDesignP 12977).tau0 c) :=
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

end BstLean.Part266.Row12977

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12978 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12978).real (BstLean.Part211.CentreSource 12978 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12978) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12978 160 (6 / 1000)
  have hj := jS_160_le (n := 12978) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12978 160 (6 / 1000) ^ 2 * 12978 /
      (((12978 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12978 160 (6 / 1000) ^ 2 * 12978 /
      (((12978 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12978 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12978 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12978) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12978 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12978

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12978) :=
  Ethm (paperCentres 12978) ∩ Ethp (paperCentres 12978)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12978)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12978)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12978) (paperCentres 12978)
  have he : exp (-(45 / 10000 * (12978 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12978 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12978) :=
  (passEvent ∩ agentEv (paperDesignP 12978) (DirectionError 12978) ∩
    agentEv (paperDesignP 12978) (CentreSources 12978 12978)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12978)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12978) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12978) hτ
  have hC := centreSources_ret_charge_row 12978 (paperDesignP 12978) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12978)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12978) (CentreSources 12978 12978)
  direction : analyticBase ⊆ agentEv (paperDesignP 12978) (DirectionError 12978)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12978)) : Set (Ret 12978) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12978)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12978)}
    (hT : (retDist (paperCentres 12978)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12978)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12978)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12978)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12978)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12978)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12978

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12978 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12978 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12978 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12978 12978 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12978)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12978)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12978
  have hb0 := BstLean.Part150.betaJ_nonneg 12978
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12978 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12978 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12978 * BstLean.Part150.betaJ 12978) * 12978) ≤
      (80996691 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12978)) * 12978 := by gcongr <;> linarith
      _ ≤ ((80996691 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12978 * 12978 *
      (1 + BstLean.Part154.deltaChi 12978 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92710557 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12978 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92710557 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12978 : ℝ) / BstLean.Part154.csC) ≤ (50049967 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12978 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50049967 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12978 : ℝ) * (80996691 / 500000) +
        2 * (1792 / 10000 / 12978) * (92710557 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (50049967 / 500000) *
          (81 / 1000 / 12978 + (1792 / 10000 / 12978) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12978

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12978
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12978 ∧
    1 ≤ gPlus 12978 ∧ gPlus 12978 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12978 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12978 : ℝ) < √(1 - 2 / (12978 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12978 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12978 (gMinus 12978) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12978 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12978 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12978 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12978)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12978 (gMinus 12978) (gPlus 12978)
      (finiteEnergy 12978 12978 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12978 (gMinus 12978) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12978 (gMinus 12978) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12978 (gMinus 12978) (54 / 100))
    (by linarith : energyRatio 12978 (gMinus 12978) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12978 (gMinus 12978) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12978 * kappa (energyRatio 12978 (gMinus 12978) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12978) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12978 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12978 12978 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12978 12978 (11 / 1000) / √12978 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12978)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12978 * kappa (energyRatio 12978 (gMinus 12978) (54 / 100))) +
      2 * √(12 * gPlus 12978) / 12978 + finiteEnergy 12978 12978 (11 / 1000) / √12978 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12978 θ ∧ meanLowerRoot 12978 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12978 - 2 / (12978 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12978 - 2 / (12978 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12978 θ ^ 2 / gPlus 12978) - 2 / (12978 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12978 * (kappa (meanLowerRoot 12978 θ ^ 2 / gPlus 12978) -
        2 / (12978 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12978) / 12978 -
        finiteEnergy 12978 12978 (11 / 1000) / √12978 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12978 θ ^ 2 / gPlus 12978 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12978)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12978 θ ^ 2 / gPlus 12978 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12978)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12978 θ ^ 2 / gPlus 12978 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12978 ^ 2 ≤
      kappa (meanLowerRoot 12978 θ ^ 2 / gPlus 12978) - 2 / (12978 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12978 *
      (kappa (meanLowerRoot 12978 θ ^ 2 / gPlus 12978) - 2 / (12978 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12978 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12978)
    linarith
  have ht : √(12 * gPlus 12978) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12978 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12978 12978 (11 / 1000) / √12978 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12978)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12978 (gMinus 12978) (gPlus 12978)
      (finiteEnergy 12978 12978 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12978) (hτ : 0 < (paperDesignP 12978).tau0 c) :
    eR c = (2 / (mA 12978 : ℝ)) *
      normSq (BstLean.Part150.bT 12978 12978 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12978).tau0 c)) /
      (2 / (12978 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12978).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12978).tau0 c))⁻¹ •
      BstLean.Part150.bT 12978 12978 (A1 c) (A2 c) c.1.2 ((paperDesignP 12978).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12978 : ℝ)) * normSq (bR c) / (2 / (12978 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12978}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12978) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12978).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12978 : ℝ) * (paperDesignP 12978).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12978 12978 c.1.2 ((paperDesignP 12978).tau0 c) :=
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

end BstLean.Part266.Row12978

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12979 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12979).real (BstLean.Part211.CentreSource 12979 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12979) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12979 160 (6 / 1000)
  have hj := jS_160_le (n := 12979) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12979 160 (6 / 1000) ^ 2 * 12979 /
      (((12979 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12979 160 (6 / 1000) ^ 2 * 12979 /
      (((12979 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12979 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12979 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12979) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12979 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12979

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12979) :=
  Ethm (paperCentres 12979) ∩ Ethp (paperCentres 12979)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12979)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12979)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12979) (paperCentres 12979)
  have he : exp (-(45 / 10000 * (12979 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12979 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12979) :=
  (passEvent ∩ agentEv (paperDesignP 12979) (DirectionError 12979) ∩
    agentEv (paperDesignP 12979) (CentreSources 12979 12979)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12979)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12979) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12979) hτ
  have hC := centreSources_ret_charge_row 12979 (paperDesignP 12979) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12979)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12979) (CentreSources 12979 12979)
  direction : analyticBase ⊆ agentEv (paperDesignP 12979) (DirectionError 12979)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12979)) : Set (Ret 12979) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12979)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12979)}
    (hT : (retDist (paperCentres 12979)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12979)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12979)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12979)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12979)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12979)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12979

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12979 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12979 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12979 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12979 12979 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12979)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12979)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12979
  have hb0 := BstLean.Part150.betaJ_nonneg 12979
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12979 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12979 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12979 * BstLean.Part150.betaJ 12979) * 12979) ≤
      (80999811 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12979)) * 12979 := by gcongr <;> linarith
      _ ≤ ((80999811 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12979 * 12979 *
      (1 + BstLean.Part154.deltaChi 12979 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185428257 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12979 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185428257 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12979 : ℝ) / BstLean.Part154.csC) ≤ (100103791 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12979 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100103791 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12979 : ℝ) * (80999811 / 500000) +
        2 * (1792 / 10000 / 12979) * (185428257 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (100103791 / 1000000) *
          (81 / 1000 / 12979 + (1792 / 10000 / 12979) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12979

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12979
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12979 ∧
    1 ≤ gPlus 12979 ∧ gPlus 12979 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12979 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12979 : ℝ) < √(1 - 2 / (12979 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12979 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12979 (gMinus 12979) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12979 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12979 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12979 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12979)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12979 (gMinus 12979) (gPlus 12979)
      (finiteEnergy 12979 12979 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12979 (gMinus 12979) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12979 (gMinus 12979) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12979 (gMinus 12979) (54 / 100))
    (by linarith : energyRatio 12979 (gMinus 12979) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12979 (gMinus 12979) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12979 * kappa (energyRatio 12979 (gMinus 12979) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12979) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12979 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12979 12979 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12979 12979 (11 / 1000) / √12979 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12979)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12979 * kappa (energyRatio 12979 (gMinus 12979) (54 / 100))) +
      2 * √(12 * gPlus 12979) / 12979 + finiteEnergy 12979 12979 (11 / 1000) / √12979 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12979 θ ∧ meanLowerRoot 12979 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12979 - 2 / (12979 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12979 - 2 / (12979 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12979 θ ^ 2 / gPlus 12979) - 2 / (12979 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12979 * (kappa (meanLowerRoot 12979 θ ^ 2 / gPlus 12979) -
        2 / (12979 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12979) / 12979 -
        finiteEnergy 12979 12979 (11 / 1000) / √12979 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12979 θ ^ 2 / gPlus 12979 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12979)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12979 θ ^ 2 / gPlus 12979 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12979)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12979 θ ^ 2 / gPlus 12979 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12979 ^ 2 ≤
      kappa (meanLowerRoot 12979 θ ^ 2 / gPlus 12979) - 2 / (12979 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12979 *
      (kappa (meanLowerRoot 12979 θ ^ 2 / gPlus 12979) - 2 / (12979 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12979 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12979)
    linarith
  have ht : √(12 * gPlus 12979) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12979 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12979 12979 (11 / 1000) / √12979 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12979)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12979 (gMinus 12979) (gPlus 12979)
      (finiteEnergy 12979 12979 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12979) (hτ : 0 < (paperDesignP 12979).tau0 c) :
    eR c = (2 / (mA 12979 : ℝ)) *
      normSq (BstLean.Part150.bT 12979 12979 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12979).tau0 c)) /
      (2 / (12979 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12979).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12979).tau0 c))⁻¹ •
      BstLean.Part150.bT 12979 12979 (A1 c) (A2 c) c.1.2 ((paperDesignP 12979).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12979 : ℝ)) * normSq (bR c) / (2 / (12979 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12979}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12979) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12979).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12979 : ℝ) * (paperDesignP 12979).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12979 12979 c.1.2 ((paperDesignP 12979).tau0 c) :=
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

end BstLean.Part266.Row12979

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12980 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12980).real (BstLean.Part211.CentreSource 12980 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12980) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12980 160 (6 / 1000)
  have hj := jS_160_le (n := 12980) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12980 160 (6 / 1000) ^ 2 * 12980 /
      (((12980 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12980 160 (6 / 1000) ^ 2 * 12980 /
      (((12980 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12980 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12980 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12980) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12980 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12980

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12980) :=
  Ethm (paperCentres 12980) ∩ Ethp (paperCentres 12980)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12980)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12980)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12980) (paperCentres 12980)
  have he : exp (-(45 / 10000 * (12980 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12980 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12980) :=
  (passEvent ∩ agentEv (paperDesignP 12980) (DirectionError 12980) ∩
    agentEv (paperDesignP 12980) (CentreSources 12980 12980)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12980)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12980) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12980) hτ
  have hC := centreSources_ret_charge_row 12980 (paperDesignP 12980) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12980)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12980) (CentreSources 12980 12980)
  direction : analyticBase ⊆ agentEv (paperDesignP 12980) (DirectionError 12980)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12980)) : Set (Ret 12980) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12980)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12980)}
    (hT : (retDist (paperCentres 12980)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12980)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12980)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12980)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12980)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12980)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12980

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12980 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12980 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12980 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12980 12980 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12980)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12980)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12980
  have hb0 := BstLean.Part150.betaJ_nonneg 12980
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12980 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12980 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12980 * BstLean.Part150.betaJ 12980) * 12980) ≤
      (162005863 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12980)) * 12980 := by gcongr <;> linarith
      _ ≤ ((162005863 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12980 * 12980 *
      (1 + BstLean.Part154.deltaChi 12980 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185435401 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12980 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185435401 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12980 : ℝ) / BstLean.Part154.csC) ≤ (100107647 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12980 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100107647 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12980 : ℝ) * (162005863 / 1000000) +
        2 * (1792 / 10000 / 12980) * (185435401 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (100107647 / 1000000) *
          (81 / 1000 / 12980 + (1792 / 10000 / 12980) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12980

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12980
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12980 ∧
    1 ≤ gPlus 12980 ∧ gPlus 12980 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12980 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12980 : ℝ) < √(1 - 2 / (12980 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12980 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12980 (gMinus 12980) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12980 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12980 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12980 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12980)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12980 (gMinus 12980) (gPlus 12980)
      (finiteEnergy 12980 12980 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12980 (gMinus 12980) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12980 (gMinus 12980) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12980 (gMinus 12980) (54 / 100))
    (by linarith : energyRatio 12980 (gMinus 12980) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12980 (gMinus 12980) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12980 * kappa (energyRatio 12980 (gMinus 12980) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12980) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12980 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12980 12980 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12980 12980 (11 / 1000) / √12980 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12980)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12980 * kappa (energyRatio 12980 (gMinus 12980) (54 / 100))) +
      2 * √(12 * gPlus 12980) / 12980 + finiteEnergy 12980 12980 (11 / 1000) / √12980 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12980 θ ∧ meanLowerRoot 12980 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12980 - 2 / (12980 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12980 - 2 / (12980 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12980 θ ^ 2 / gPlus 12980) - 2 / (12980 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12980 * (kappa (meanLowerRoot 12980 θ ^ 2 / gPlus 12980) -
        2 / (12980 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12980) / 12980 -
        finiteEnergy 12980 12980 (11 / 1000) / √12980 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12980 θ ^ 2 / gPlus 12980 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12980)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12980 θ ^ 2 / gPlus 12980 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12980)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12980 θ ^ 2 / gPlus 12980 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12980 ^ 2 ≤
      kappa (meanLowerRoot 12980 θ ^ 2 / gPlus 12980) - 2 / (12980 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12980 *
      (kappa (meanLowerRoot 12980 θ ^ 2 / gPlus 12980) - 2 / (12980 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12980 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12980)
    linarith
  have ht : √(12 * gPlus 12980) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12980 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12980 12980 (11 / 1000) / √12980 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12980)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12980 (gMinus 12980) (gPlus 12980)
      (finiteEnergy 12980 12980 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12980) (hτ : 0 < (paperDesignP 12980).tau0 c) :
    eR c = (2 / (mA 12980 : ℝ)) *
      normSq (BstLean.Part150.bT 12980 12980 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12980).tau0 c)) /
      (2 / (12980 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12980).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12980).tau0 c))⁻¹ •
      BstLean.Part150.bT 12980 12980 (A1 c) (A2 c) c.1.2 ((paperDesignP 12980).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12980 : ℝ)) * normSq (bR c) / (2 / (12980 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12980}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12980) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12980).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12980 : ℝ) * (paperDesignP 12980).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12980 12980 c.1.2 ((paperDesignP 12980).tau0 c) :=
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

end BstLean.Part266.Row12980

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12981 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12981).real (BstLean.Part211.CentreSource 12981 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12981) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12981 160 (6 / 1000)
  have hj := jS_160_le (n := 12981) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12981 160 (6 / 1000) ^ 2 * 12981 /
      (((12981 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12981 160 (6 / 1000) ^ 2 * 12981 /
      (((12981 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12981 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12981 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12981) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12981 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12981

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12981) :=
  Ethm (paperCentres 12981) ∩ Ethp (paperCentres 12981)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12981)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12981)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12981) (paperCentres 12981)
  have he : exp (-(45 / 10000 * (12981 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12981 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12981) :=
  (passEvent ∩ agentEv (paperDesignP 12981) (DirectionError 12981) ∩
    agentEv (paperDesignP 12981) (CentreSources 12981 12981)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12981)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12981) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12981) hτ
  have hC := centreSources_ret_charge_row 12981 (paperDesignP 12981) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12981)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12981) (CentreSources 12981 12981)
  direction : analyticBase ⊆ agentEv (paperDesignP 12981) (DirectionError 12981)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12981)) : Set (Ret 12981) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12981)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12981)}
    (hT : (retDist (paperCentres 12981)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12981)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12981)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12981)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12981)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12981)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12981

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12981 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12981 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12981 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12981 12981 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12981)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12981)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12981
  have hb0 := BstLean.Part150.betaJ_nonneg 12981
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12981 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12981 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12981 * BstLean.Part150.betaJ 12981) * 12981) ≤
      (20251513 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12981)) * 12981 := by gcongr <;> linarith
      _ ≤ ((20251513 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12981 * 12981 *
      (1 + BstLean.Part154.deltaChi 12981 12 + 2 / π) / BstLean.Part154.csC) ≤
      (11590159 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12981 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((11590159 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12981 : ℝ) / BstLean.Part154.csC) ≤ (100111503 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12981 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100111503 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12981 : ℝ) * (20251513 / 125000) +
        2 * (1792 / 10000 / 12981) * (11590159 / 62500) +
        4 * (1 / 2.506628) * 1.036505 * (100111503 / 1000000) *
          (81 / 1000 / 12981 + (1792 / 10000 / 12981) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12981

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12981
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12981 ∧
    1 ≤ gPlus 12981 ∧ gPlus 12981 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12981 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12981 : ℝ) < √(1 - 2 / (12981 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12981 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12981 (gMinus 12981) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12981 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12981 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12981 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12981)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12981 (gMinus 12981) (gPlus 12981)
      (finiteEnergy 12981 12981 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12981 (gMinus 12981) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12981 (gMinus 12981) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12981 (gMinus 12981) (54 / 100))
    (by linarith : energyRatio 12981 (gMinus 12981) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12981 (gMinus 12981) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12981 * kappa (energyRatio 12981 (gMinus 12981) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12981) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12981 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12981 12981 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12981 12981 (11 / 1000) / √12981 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12981)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12981 * kappa (energyRatio 12981 (gMinus 12981) (54 / 100))) +
      2 * √(12 * gPlus 12981) / 12981 + finiteEnergy 12981 12981 (11 / 1000) / √12981 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12981 θ ∧ meanLowerRoot 12981 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12981 - 2 / (12981 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12981 - 2 / (12981 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12981 θ ^ 2 / gPlus 12981) - 2 / (12981 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12981 * (kappa (meanLowerRoot 12981 θ ^ 2 / gPlus 12981) -
        2 / (12981 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12981) / 12981 -
        finiteEnergy 12981 12981 (11 / 1000) / √12981 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12981 θ ^ 2 / gPlus 12981 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12981)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12981 θ ^ 2 / gPlus 12981 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12981)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12981 θ ^ 2 / gPlus 12981 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12981 ^ 2 ≤
      kappa (meanLowerRoot 12981 θ ^ 2 / gPlus 12981) - 2 / (12981 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12981 *
      (kappa (meanLowerRoot 12981 θ ^ 2 / gPlus 12981) - 2 / (12981 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12981 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12981)
    linarith
  have ht : √(12 * gPlus 12981) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12981 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12981 12981 (11 / 1000) / √12981 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12981)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12981 (gMinus 12981) (gPlus 12981)
      (finiteEnergy 12981 12981 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12981) (hτ : 0 < (paperDesignP 12981).tau0 c) :
    eR c = (2 / (mA 12981 : ℝ)) *
      normSq (BstLean.Part150.bT 12981 12981 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12981).tau0 c)) /
      (2 / (12981 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12981).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12981).tau0 c))⁻¹ •
      BstLean.Part150.bT 12981 12981 (A1 c) (A2 c) c.1.2 ((paperDesignP 12981).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12981 : ℝ)) * normSq (bR c) / (2 / (12981 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12981}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12981) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12981).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12981 : ℝ) * (paperDesignP 12981).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12981 12981 c.1.2 ((paperDesignP 12981).tau0 c) :=
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

end BstLean.Part266.Row12981

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12982 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12982).real (BstLean.Part211.CentreSource 12982 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12982) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12982 160 (6 / 1000)
  have hj := jS_160_le (n := 12982) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12982 160 (6 / 1000) ^ 2 * 12982 /
      (((12982 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12982 160 (6 / 1000) ^ 2 * 12982 /
      (((12982 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12982 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12982 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12982) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12982 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12982

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12982) :=
  Ethm (paperCentres 12982) ∩ Ethp (paperCentres 12982)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12982)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12982)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12982) (paperCentres 12982)
  have he : exp (-(45 / 10000 * (12982 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12982 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12982) :=
  (passEvent ∩ agentEv (paperDesignP 12982) (DirectionError 12982) ∩
    agentEv (paperDesignP 12982) (CentreSources 12982 12982)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12982)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12982) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12982) hτ
  have hC := centreSources_ret_charge_row 12982 (paperDesignP 12982) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12982)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12982) (CentreSources 12982 12982)
  direction : analyticBase ⊆ agentEv (paperDesignP 12982) (DirectionError 12982)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12982)) : Set (Ret 12982) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12982)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12982)}
    (hT : (retDist (paperCentres 12982)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12982)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12982)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12982)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12982)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12982)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12982

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12982 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12982 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12982 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12982 12982 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12982)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12982)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12982
  have hb0 := BstLean.Part150.betaJ_nonneg 12982
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12982 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12982 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12982 * BstLean.Part150.betaJ 12982) * 12982) ≤
      (20252293 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12982)) * 12982 := by gcongr <;> linarith
      _ ≤ ((20252293 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12982 * 12982 *
      (1 + BstLean.Part154.deltaChi 12982 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92724843 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12982 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92724843 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12982 : ℝ) / BstLean.Part154.csC) ≤ (100115359 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12982 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100115359 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12982 : ℝ) * (20252293 / 125000) +
        2 * (1792 / 10000 / 12982) * (92724843 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100115359 / 1000000) *
          (81 / 1000 / 12982 + (1792 / 10000 / 12982) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12982

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12982
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12982 ∧
    1 ≤ gPlus 12982 ∧ gPlus 12982 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12982 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12982 : ℝ) < √(1 - 2 / (12982 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12982 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12982 (gMinus 12982) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12982 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12982 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12982 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12982)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12982 (gMinus 12982) (gPlus 12982)
      (finiteEnergy 12982 12982 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12982 (gMinus 12982) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12982 (gMinus 12982) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12982 (gMinus 12982) (54 / 100))
    (by linarith : energyRatio 12982 (gMinus 12982) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12982 (gMinus 12982) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12982 * kappa (energyRatio 12982 (gMinus 12982) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12982) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12982 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12982 12982 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12982 12982 (11 / 1000) / √12982 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12982)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12982 * kappa (energyRatio 12982 (gMinus 12982) (54 / 100))) +
      2 * √(12 * gPlus 12982) / 12982 + finiteEnergy 12982 12982 (11 / 1000) / √12982 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12982 θ ∧ meanLowerRoot 12982 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12982 - 2 / (12982 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12982 - 2 / (12982 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12982 θ ^ 2 / gPlus 12982) - 2 / (12982 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12982 * (kappa (meanLowerRoot 12982 θ ^ 2 / gPlus 12982) -
        2 / (12982 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12982) / 12982 -
        finiteEnergy 12982 12982 (11 / 1000) / √12982 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12982 θ ^ 2 / gPlus 12982 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12982)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12982 θ ^ 2 / gPlus 12982 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12982)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12982 θ ^ 2 / gPlus 12982 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12982 ^ 2 ≤
      kappa (meanLowerRoot 12982 θ ^ 2 / gPlus 12982) - 2 / (12982 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12982 *
      (kappa (meanLowerRoot 12982 θ ^ 2 / gPlus 12982) - 2 / (12982 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12982 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12982)
    linarith
  have ht : √(12 * gPlus 12982) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12982 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12982 12982 (11 / 1000) / √12982 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12982)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12982 (gMinus 12982) (gPlus 12982)
      (finiteEnergy 12982 12982 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12982) (hτ : 0 < (paperDesignP 12982).tau0 c) :
    eR c = (2 / (mA 12982 : ℝ)) *
      normSq (BstLean.Part150.bT 12982 12982 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12982).tau0 c)) /
      (2 / (12982 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12982).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12982).tau0 c))⁻¹ •
      BstLean.Part150.bT 12982 12982 (A1 c) (A2 c) c.1.2 ((paperDesignP 12982).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12982 : ℝ)) * normSq (bR c) / (2 / (12982 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12982}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12982) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12982).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12982 : ℝ) * (paperDesignP 12982).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12982 12982 c.1.2 ((paperDesignP 12982).tau0 c) :=
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

end BstLean.Part266.Row12982

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12983 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12983).real (BstLean.Part211.CentreSource 12983 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12983) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12983 160 (6 / 1000)
  have hj := jS_160_le (n := 12983) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12983 160 (6 / 1000) ^ 2 * 12983 /
      (((12983 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12983 160 (6 / 1000) ^ 2 * 12983 /
      (((12983 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12983 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12983 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12983) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12983 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12983

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12983) :=
  Ethm (paperCentres 12983) ∩ Ethp (paperCentres 12983)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12983)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12983)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12983) (paperCentres 12983)
  have he : exp (-(45 / 10000 * (12983 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12983 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12983) :=
  (passEvent ∩ agentEv (paperDesignP 12983) (DirectionError 12983) ∩
    agentEv (paperDesignP 12983) (CentreSources 12983 12983)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12983)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12983) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12983) hτ
  have hC := centreSources_ret_charge_row 12983 (paperDesignP 12983) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12983)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12983) (CentreSources 12983 12983)
  direction : analyticBase ⊆ agentEv (paperDesignP 12983) (DirectionError 12983)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12983)) : Set (Ret 12983) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12983)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12983)}
    (hT : (retDist (paperCentres 12983)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12983)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12983)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12983)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12983)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12983)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12983

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12983 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12983 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12983 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12983 12983 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12983)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12983)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12983
  have hb0 := BstLean.Part150.betaJ_nonneg 12983
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12983 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12983 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12983 * BstLean.Part150.betaJ 12983) * 12983) ≤
      (20253073 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12983)) * 12983 := by gcongr <;> linarith
      _ ≤ ((20253073 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12983 * 12983 *
      (1 + BstLean.Part154.deltaChi 12983 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185456829 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12983 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185456829 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12983 : ℝ) / BstLean.Part154.csC) ≤ (20023843 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12983 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((20023843 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12983 : ℝ) * (20253073 / 125000) +
        2 * (1792 / 10000 / 12983) * (185456829 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (20023843 / 200000) *
          (81 / 1000 / 12983 + (1792 / 10000 / 12983) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12983

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12983
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12983 ∧
    1 ≤ gPlus 12983 ∧ gPlus 12983 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12983 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12983 : ℝ) < √(1 - 2 / (12983 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12983 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12983 (gMinus 12983) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12983 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12983 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12983 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12983)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12983 (gMinus 12983) (gPlus 12983)
      (finiteEnergy 12983 12983 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12983 (gMinus 12983) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12983 (gMinus 12983) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12983 (gMinus 12983) (54 / 100))
    (by linarith : energyRatio 12983 (gMinus 12983) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12983 (gMinus 12983) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12983 * kappa (energyRatio 12983 (gMinus 12983) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12983) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12983 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12983 12983 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12983 12983 (11 / 1000) / √12983 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12983)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12983 * kappa (energyRatio 12983 (gMinus 12983) (54 / 100))) +
      2 * √(12 * gPlus 12983) / 12983 + finiteEnergy 12983 12983 (11 / 1000) / √12983 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12983 θ ∧ meanLowerRoot 12983 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12983 - 2 / (12983 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12983 - 2 / (12983 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12983 θ ^ 2 / gPlus 12983) - 2 / (12983 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12983 * (kappa (meanLowerRoot 12983 θ ^ 2 / gPlus 12983) -
        2 / (12983 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12983) / 12983 -
        finiteEnergy 12983 12983 (11 / 1000) / √12983 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12983 θ ^ 2 / gPlus 12983 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12983)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12983 θ ^ 2 / gPlus 12983 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12983)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12983 θ ^ 2 / gPlus 12983 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12983 ^ 2 ≤
      kappa (meanLowerRoot 12983 θ ^ 2 / gPlus 12983) - 2 / (12983 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12983 *
      (kappa (meanLowerRoot 12983 θ ^ 2 / gPlus 12983) - 2 / (12983 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12983 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12983)
    linarith
  have ht : √(12 * gPlus 12983) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12983 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12983 12983 (11 / 1000) / √12983 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12983)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12983 (gMinus 12983) (gPlus 12983)
      (finiteEnergy 12983 12983 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12983) (hτ : 0 < (paperDesignP 12983).tau0 c) :
    eR c = (2 / (mA 12983 : ℝ)) *
      normSq (BstLean.Part150.bT 12983 12983 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12983).tau0 c)) /
      (2 / (12983 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12983).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12983).tau0 c))⁻¹ •
      BstLean.Part150.bT 12983 12983 (A1 c) (A2 c) c.1.2 ((paperDesignP 12983).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12983 : ℝ)) * normSq (bR c) / (2 / (12983 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12983}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12983) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12983).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12983 : ℝ) * (paperDesignP 12983).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12983 12983 c.1.2 ((paperDesignP 12983).tau0 c) :=
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

end BstLean.Part266.Row12983

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12984 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12984).real (BstLean.Part211.CentreSource 12984 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12984) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12984 160 (6 / 1000)
  have hj := jS_160_le (n := 12984) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12984 160 (6 / 1000) ^ 2 * 12984 /
      (((12984 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12984 160 (6 / 1000) ^ 2 * 12984 /
      (((12984 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12984 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12984 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12984) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12984 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12984

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12984) :=
  Ethm (paperCentres 12984) ∩ Ethp (paperCentres 12984)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12984)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12984)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12984) (paperCentres 12984)
  have he : exp (-(45 / 10000 * (12984 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12984 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12984) :=
  (passEvent ∩ agentEv (paperDesignP 12984) (DirectionError 12984) ∩
    agentEv (paperDesignP 12984) (CentreSources 12984 12984)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12984)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12984) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12984) hτ
  have hC := centreSources_ret_charge_row 12984 (paperDesignP 12984) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12984)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12984) (CentreSources 12984 12984)
  direction : analyticBase ⊆ agentEv (paperDesignP 12984) (DirectionError 12984)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12984)) : Set (Ret 12984) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12984)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12984)}
    (hT : (retDist (paperCentres 12984)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12984)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12984)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12984)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12984)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12984)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12984

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12984 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12984 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12984 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12984 12984 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12984)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12984)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12984
  have hb0 := BstLean.Part150.betaJ_nonneg 12984
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12984 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12984 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12984 * BstLean.Part150.betaJ 12984) * 12984) ≤
      (162030823 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12984)) * 12984 := by gcongr <;> linarith
      _ ≤ ((162030823 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12984 * 12984 *
      (1 + BstLean.Part154.deltaChi 12984 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185463971 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12984 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185463971 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12984 : ℝ) / BstLean.Part154.csC) ≤ (100123071 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12984 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100123071 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12984 : ℝ) * (162030823 / 1000000) +
        2 * (1792 / 10000 / 12984) * (185463971 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (100123071 / 1000000) *
          (81 / 1000 / 12984 + (1792 / 10000 / 12984) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12984

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12984
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12984 ∧
    1 ≤ gPlus 12984 ∧ gPlus 12984 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12984 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12984 : ℝ) < √(1 - 2 / (12984 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12984 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12984 (gMinus 12984) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12984 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12984 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12984 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12984)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12984 (gMinus 12984) (gPlus 12984)
      (finiteEnergy 12984 12984 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12984 (gMinus 12984) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12984 (gMinus 12984) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12984 (gMinus 12984) (54 / 100))
    (by linarith : energyRatio 12984 (gMinus 12984) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12984 (gMinus 12984) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12984 * kappa (energyRatio 12984 (gMinus 12984) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12984) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12984 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12984 12984 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12984 12984 (11 / 1000) / √12984 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12984)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12984 * kappa (energyRatio 12984 (gMinus 12984) (54 / 100))) +
      2 * √(12 * gPlus 12984) / 12984 + finiteEnergy 12984 12984 (11 / 1000) / √12984 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12984 θ ∧ meanLowerRoot 12984 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12984 - 2 / (12984 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12984 - 2 / (12984 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12984 θ ^ 2 / gPlus 12984) - 2 / (12984 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12984 * (kappa (meanLowerRoot 12984 θ ^ 2 / gPlus 12984) -
        2 / (12984 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12984) / 12984 -
        finiteEnergy 12984 12984 (11 / 1000) / √12984 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12984 θ ^ 2 / gPlus 12984 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12984)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12984 θ ^ 2 / gPlus 12984 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12984)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12984 θ ^ 2 / gPlus 12984 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12984 ^ 2 ≤
      kappa (meanLowerRoot 12984 θ ^ 2 / gPlus 12984) - 2 / (12984 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12984 *
      (kappa (meanLowerRoot 12984 θ ^ 2 / gPlus 12984) - 2 / (12984 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12984 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12984)
    linarith
  have ht : √(12 * gPlus 12984) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12984 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12984 12984 (11 / 1000) / √12984 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12984)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12984 (gMinus 12984) (gPlus 12984)
      (finiteEnergy 12984 12984 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12984) (hτ : 0 < (paperDesignP 12984).tau0 c) :
    eR c = (2 / (mA 12984 : ℝ)) *
      normSq (BstLean.Part150.bT 12984 12984 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12984).tau0 c)) /
      (2 / (12984 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12984).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12984).tau0 c))⁻¹ •
      BstLean.Part150.bT 12984 12984 (A1 c) (A2 c) c.1.2 ((paperDesignP 12984).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12984 : ℝ)) * normSq (bR c) / (2 / (12984 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12984}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12984) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12984).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12984 : ℝ) * (paperDesignP 12984).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12984 12984 c.1.2 ((paperDesignP 12984).tau0 c) :=
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

end BstLean.Part266.Row12984

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12985 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12985).real (BstLean.Part211.CentreSource 12985 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12985) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12985 160 (6 / 1000)
  have hj := jS_160_le (n := 12985) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12985 160 (6 / 1000) ^ 2 * 12985 /
      (((12985 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12985 160 (6 / 1000) ^ 2 * 12985 /
      (((12985 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12985 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12985 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12985) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12985 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12985

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12985) :=
  Ethm (paperCentres 12985) ∩ Ethp (paperCentres 12985)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12985)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12985)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12985) (paperCentres 12985)
  have he : exp (-(45 / 10000 * (12985 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12985 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12985) :=
  (passEvent ∩ agentEv (paperDesignP 12985) (DirectionError 12985) ∩
    agentEv (paperDesignP 12985) (CentreSources 12985 12985)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12985)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12985) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12985) hτ
  have hC := centreSources_ret_charge_row 12985 (paperDesignP 12985) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12985)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12985) (CentreSources 12985 12985)
  direction : analyticBase ⊆ agentEv (paperDesignP 12985) (DirectionError 12985)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12985)) : Set (Ret 12985) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12985)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12985)}
    (hT : (retDist (paperCentres 12985)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12985)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12985)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12985)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12985)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12985)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12985

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12985 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12985 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12985 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12985 12985 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12985)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12985)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12985
  have hb0 := BstLean.Part150.betaJ_nonneg 12985
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12985 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12985 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12985 * BstLean.Part150.betaJ 12985) * 12985) ≤
      (162037063 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12985)) * 12985 := by gcongr <;> linarith
      _ ≤ ((162037063 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12985 * 12985 *
      (1 + BstLean.Part154.deltaChi 12985 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185471113 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12985 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185471113 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12985 : ℝ) / BstLean.Part154.csC) ≤ (50063463 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12985 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50063463 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12985 : ℝ) * (162037063 / 1000000) +
        2 * (1792 / 10000 / 12985) * (185471113 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (50063463 / 500000) *
          (81 / 1000 / 12985 + (1792 / 10000 / 12985) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12985

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12985
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12985 ∧
    1 ≤ gPlus 12985 ∧ gPlus 12985 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12985 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12985 : ℝ) < √(1 - 2 / (12985 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12985 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12985 (gMinus 12985) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12985 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12985 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12985 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12985)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12985 (gMinus 12985) (gPlus 12985)
      (finiteEnergy 12985 12985 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12985 (gMinus 12985) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12985 (gMinus 12985) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12985 (gMinus 12985) (54 / 100))
    (by linarith : energyRatio 12985 (gMinus 12985) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12985 (gMinus 12985) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12985 * kappa (energyRatio 12985 (gMinus 12985) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12985) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12985 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12985 12985 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12985 12985 (11 / 1000) / √12985 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12985)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12985 * kappa (energyRatio 12985 (gMinus 12985) (54 / 100))) +
      2 * √(12 * gPlus 12985) / 12985 + finiteEnergy 12985 12985 (11 / 1000) / √12985 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12985 θ ∧ meanLowerRoot 12985 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12985 - 2 / (12985 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12985 - 2 / (12985 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12985 θ ^ 2 / gPlus 12985) - 2 / (12985 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12985 * (kappa (meanLowerRoot 12985 θ ^ 2 / gPlus 12985) -
        2 / (12985 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12985) / 12985 -
        finiteEnergy 12985 12985 (11 / 1000) / √12985 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12985 θ ^ 2 / gPlus 12985 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12985)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12985 θ ^ 2 / gPlus 12985 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12985)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12985 θ ^ 2 / gPlus 12985 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12985 ^ 2 ≤
      kappa (meanLowerRoot 12985 θ ^ 2 / gPlus 12985) - 2 / (12985 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12985 *
      (kappa (meanLowerRoot 12985 θ ^ 2 / gPlus 12985) - 2 / (12985 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12985 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12985)
    linarith
  have ht : √(12 * gPlus 12985) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12985 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12985 12985 (11 / 1000) / √12985 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12985)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12985 (gMinus 12985) (gPlus 12985)
      (finiteEnergy 12985 12985 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12985) (hτ : 0 < (paperDesignP 12985).tau0 c) :
    eR c = (2 / (mA 12985 : ℝ)) *
      normSq (BstLean.Part150.bT 12985 12985 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12985).tau0 c)) /
      (2 / (12985 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12985).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12985).tau0 c))⁻¹ •
      BstLean.Part150.bT 12985 12985 (A1 c) (A2 c) c.1.2 ((paperDesignP 12985).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12985 : ℝ)) * normSq (bR c) / (2 / (12985 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12985}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12985) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12985).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12985 : ℝ) * (paperDesignP 12985).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12985 12985 c.1.2 ((paperDesignP 12985).tau0 c) :=
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

end BstLean.Part266.Row12985

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12986 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12986).real (BstLean.Part211.CentreSource 12986 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12986) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12986 160 (6 / 1000)
  have hj := jS_160_le (n := 12986) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12986 160 (6 / 1000) ^ 2 * 12986 /
      (((12986 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12986 160 (6 / 1000) ^ 2 * 12986 /
      (((12986 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12986 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12986 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12986) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12986 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12986

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12986) :=
  Ethm (paperCentres 12986) ∩ Ethp (paperCentres 12986)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12986)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12986)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12986) (paperCentres 12986)
  have he : exp (-(45 / 10000 * (12986 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12986 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12986) :=
  (passEvent ∩ agentEv (paperDesignP 12986) (DirectionError 12986) ∩
    agentEv (paperDesignP 12986) (CentreSources 12986 12986)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12986)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12986) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12986) hτ
  have hC := centreSources_ret_charge_row 12986 (paperDesignP 12986) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12986)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12986) (CentreSources 12986 12986)
  direction : analyticBase ⊆ agentEv (paperDesignP 12986) (DirectionError 12986)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12986)) : Set (Ret 12986) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12986)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12986)}
    (hT : (retDist (paperCentres 12986)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12986)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12986)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12986)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12986)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12986)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12986

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12986 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12986 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12986 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12986 12986 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12986)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12986)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12986
  have hb0 := BstLean.Part150.betaJ_nonneg 12986
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12986 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12986 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12986 * BstLean.Part150.betaJ 12986) * 12986) ≤
      (81021651 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12986)) * 12986 := by gcongr <;> linarith
      _ ≤ ((81021651 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12986 * 12986 *
      (1 + BstLean.Part154.deltaChi 12986 12 + 2 / π) / BstLean.Part154.csC) ≤
      (37095651 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12986 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((37095651 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12986 : ℝ) / BstLean.Part154.csC) ≤ (50065391 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12986 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50065391 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12986 : ℝ) * (81021651 / 500000) +
        2 * (1792 / 10000 / 12986) * (37095651 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (50065391 / 500000) *
          (81 / 1000 / 12986 + (1792 / 10000 / 12986) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12986

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12986
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12986 ∧
    1 ≤ gPlus 12986 ∧ gPlus 12986 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12986 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12986 : ℝ) < √(1 - 2 / (12986 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12986 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12986 (gMinus 12986) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12986 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12986 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12986 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12986)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12986 (gMinus 12986) (gPlus 12986)
      (finiteEnergy 12986 12986 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12986 (gMinus 12986) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12986 (gMinus 12986) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12986 (gMinus 12986) (54 / 100))
    (by linarith : energyRatio 12986 (gMinus 12986) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12986 (gMinus 12986) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12986 * kappa (energyRatio 12986 (gMinus 12986) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12986) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12986 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12986 12986 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12986 12986 (11 / 1000) / √12986 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12986)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12986 * kappa (energyRatio 12986 (gMinus 12986) (54 / 100))) +
      2 * √(12 * gPlus 12986) / 12986 + finiteEnergy 12986 12986 (11 / 1000) / √12986 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12986 θ ∧ meanLowerRoot 12986 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12986 - 2 / (12986 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12986 - 2 / (12986 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12986 θ ^ 2 / gPlus 12986) - 2 / (12986 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12986 * (kappa (meanLowerRoot 12986 θ ^ 2 / gPlus 12986) -
        2 / (12986 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12986) / 12986 -
        finiteEnergy 12986 12986 (11 / 1000) / √12986 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12986 θ ^ 2 / gPlus 12986 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12986)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12986 θ ^ 2 / gPlus 12986 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12986)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12986 θ ^ 2 / gPlus 12986 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12986 ^ 2 ≤
      kappa (meanLowerRoot 12986 θ ^ 2 / gPlus 12986) - 2 / (12986 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12986 *
      (kappa (meanLowerRoot 12986 θ ^ 2 / gPlus 12986) - 2 / (12986 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12986 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12986)
    linarith
  have ht : √(12 * gPlus 12986) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12986 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12986 12986 (11 / 1000) / √12986 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12986)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12986 (gMinus 12986) (gPlus 12986)
      (finiteEnergy 12986 12986 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12986) (hτ : 0 < (paperDesignP 12986).tau0 c) :
    eR c = (2 / (mA 12986 : ℝ)) *
      normSq (BstLean.Part150.bT 12986 12986 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12986).tau0 c)) /
      (2 / (12986 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12986).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12986).tau0 c))⁻¹ •
      BstLean.Part150.bT 12986 12986 (A1 c) (A2 c) c.1.2 ((paperDesignP 12986).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12986 : ℝ)) * normSq (bR c) / (2 / (12986 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12986}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12986) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12986).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12986 : ℝ) * (paperDesignP 12986).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12986 12986 c.1.2 ((paperDesignP 12986).tau0 c) :=
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

end BstLean.Part266.Row12986

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12987 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12987).real (BstLean.Part211.CentreSource 12987 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12987) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12987 160 (6 / 1000)
  have hj := jS_160_le (n := 12987) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12987 160 (6 / 1000) ^ 2 * 12987 /
      (((12987 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12987 160 (6 / 1000) ^ 2 * 12987 /
      (((12987 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12987 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12987 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12987) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12987 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12987

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12987) :=
  Ethm (paperCentres 12987) ∩ Ethp (paperCentres 12987)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12987)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12987)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12987) (paperCentres 12987)
  have he : exp (-(45 / 10000 * (12987 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12987 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12987) :=
  (passEvent ∩ agentEv (paperDesignP 12987) (DirectionError 12987) ∩
    agentEv (paperDesignP 12987) (CentreSources 12987 12987)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12987)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12987) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12987) hτ
  have hC := centreSources_ret_charge_row 12987 (paperDesignP 12987) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12987)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12987) (CentreSources 12987 12987)
  direction : analyticBase ⊆ agentEv (paperDesignP 12987) (DirectionError 12987)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12987)) : Set (Ret 12987) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12987)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12987)}
    (hT : (retDist (paperCentres 12987)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12987)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12987)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12987)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12987)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12987)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12987

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12987 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12987 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12987 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12987 12987 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12987)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12987)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12987
  have hb0 := BstLean.Part150.betaJ_nonneg 12987
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12987 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12987 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12987 * BstLean.Part150.betaJ 12987) * 12987) ≤
      (162049541 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12987)) * 12987 := by gcongr <;> linarith
      _ ≤ ((162049541 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12987 * 12987 *
      (1 + BstLean.Part154.deltaChi 12987 12 + 2 / π) / BstLean.Part154.csC) ≤
      (46371349 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12987 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((46371349 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12987 : ℝ) / BstLean.Part154.csC) ≤ (100134637 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12987 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100134637 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12987 : ℝ) * (162049541 / 1000000) +
        2 * (1792 / 10000 / 12987) * (46371349 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (100134637 / 1000000) *
          (81 / 1000 / 12987 + (1792 / 10000 / 12987) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12987

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12987
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12987 ∧
    1 ≤ gPlus 12987 ∧ gPlus 12987 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12987 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12987 : ℝ) < √(1 - 2 / (12987 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12987 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12987 (gMinus 12987) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12987 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12987 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12987 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12987)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12987 (gMinus 12987) (gPlus 12987)
      (finiteEnergy 12987 12987 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12987 (gMinus 12987) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12987 (gMinus 12987) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12987 (gMinus 12987) (54 / 100))
    (by linarith : energyRatio 12987 (gMinus 12987) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12987 (gMinus 12987) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12987 * kappa (energyRatio 12987 (gMinus 12987) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12987) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12987 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12987 12987 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12987 12987 (11 / 1000) / √12987 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12987)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12987 * kappa (energyRatio 12987 (gMinus 12987) (54 / 100))) +
      2 * √(12 * gPlus 12987) / 12987 + finiteEnergy 12987 12987 (11 / 1000) / √12987 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12987 θ ∧ meanLowerRoot 12987 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12987 - 2 / (12987 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12987 - 2 / (12987 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12987 θ ^ 2 / gPlus 12987) - 2 / (12987 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12987 * (kappa (meanLowerRoot 12987 θ ^ 2 / gPlus 12987) -
        2 / (12987 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12987) / 12987 -
        finiteEnergy 12987 12987 (11 / 1000) / √12987 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12987 θ ^ 2 / gPlus 12987 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12987)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12987 θ ^ 2 / gPlus 12987 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12987)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12987 θ ^ 2 / gPlus 12987 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12987 ^ 2 ≤
      kappa (meanLowerRoot 12987 θ ^ 2 / gPlus 12987) - 2 / (12987 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12987 *
      (kappa (meanLowerRoot 12987 θ ^ 2 / gPlus 12987) - 2 / (12987 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12987 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12987)
    linarith
  have ht : √(12 * gPlus 12987) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12987 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12987 12987 (11 / 1000) / √12987 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12987)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12987 (gMinus 12987) (gPlus 12987)
      (finiteEnergy 12987 12987 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12987) (hτ : 0 < (paperDesignP 12987).tau0 c) :
    eR c = (2 / (mA 12987 : ℝ)) *
      normSq (BstLean.Part150.bT 12987 12987 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12987).tau0 c)) /
      (2 / (12987 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12987).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12987).tau0 c))⁻¹ •
      BstLean.Part150.bT 12987 12987 (A1 c) (A2 c) c.1.2 ((paperDesignP 12987).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12987 : ℝ)) * normSq (bR c) / (2 / (12987 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12987}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12987) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12987).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12987 : ℝ) * (paperDesignP 12987).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12987 12987 c.1.2 ((paperDesignP 12987).tau0 c) :=
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

end BstLean.Part266.Row12987

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12988 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12988).real (BstLean.Part211.CentreSource 12988 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12988) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12988 160 (6 / 1000)
  have hj := jS_160_le (n := 12988) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12988 160 (6 / 1000) ^ 2 * 12988 /
      (((12988 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12988 160 (6 / 1000) ^ 2 * 12988 /
      (((12988 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12988 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12988 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12988) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12988 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12988

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12988) :=
  Ethm (paperCentres 12988) ∩ Ethp (paperCentres 12988)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12988)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12988)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12988) (paperCentres 12988)
  have he : exp (-(45 / 10000 * (12988 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12988 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12988) :=
  (passEvent ∩ agentEv (paperDesignP 12988) (DirectionError 12988) ∩
    agentEv (paperDesignP 12988) (CentreSources 12988 12988)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12988)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12988) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12988) hτ
  have hC := centreSources_ret_charge_row 12988 (paperDesignP 12988) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12988)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12988) (CentreSources 12988 12988)
  direction : analyticBase ⊆ agentEv (paperDesignP 12988) (DirectionError 12988)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12988)) : Set (Ret 12988) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12988)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12988)}
    (hT : (retDist (paperCentres 12988)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12988)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12988)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12988)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12988)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12988)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12988

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12988 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12988 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12988 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12988 12988 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12988)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12988)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12988
  have hb0 := BstLean.Part150.betaJ_nonneg 12988
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12988 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12988 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12988 * BstLean.Part150.betaJ 12988) * 12988) ≤
      (8102789 / 50000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12988)) * 12988 := by gcongr <;> linarith
      _ ≤ ((8102789 / 50000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12988 * 12988 *
      (1 + BstLean.Part154.deltaChi 12988 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185492537 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12988 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185492537 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12988 : ℝ) / BstLean.Part154.csC) ≤ (25034623 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12988 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((25034623 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12988 : ℝ) * (8102789 / 50000) +
        2 * (1792 / 10000 / 12988) * (185492537 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (25034623 / 250000) *
          (81 / 1000 / 12988 + (1792 / 10000 / 12988) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12988

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12988
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12988 ∧
    1 ≤ gPlus 12988 ∧ gPlus 12988 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12988 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12988 : ℝ) < √(1 - 2 / (12988 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12988 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12988 (gMinus 12988) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12988 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12988 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12988 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12988)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12988 (gMinus 12988) (gPlus 12988)
      (finiteEnergy 12988 12988 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12988 (gMinus 12988) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12988 (gMinus 12988) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12988 (gMinus 12988) (54 / 100))
    (by linarith : energyRatio 12988 (gMinus 12988) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12988 (gMinus 12988) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12988 * kappa (energyRatio 12988 (gMinus 12988) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12988) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12988 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12988 12988 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12988 12988 (11 / 1000) / √12988 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12988)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12988 * kappa (energyRatio 12988 (gMinus 12988) (54 / 100))) +
      2 * √(12 * gPlus 12988) / 12988 + finiteEnergy 12988 12988 (11 / 1000) / √12988 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12988 θ ∧ meanLowerRoot 12988 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12988 - 2 / (12988 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12988 - 2 / (12988 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12988 θ ^ 2 / gPlus 12988) - 2 / (12988 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12988 * (kappa (meanLowerRoot 12988 θ ^ 2 / gPlus 12988) -
        2 / (12988 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12988) / 12988 -
        finiteEnergy 12988 12988 (11 / 1000) / √12988 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12988 θ ^ 2 / gPlus 12988 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12988)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12988 θ ^ 2 / gPlus 12988 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12988)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12988 θ ^ 2 / gPlus 12988 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12988 ^ 2 ≤
      kappa (meanLowerRoot 12988 θ ^ 2 / gPlus 12988) - 2 / (12988 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12988 *
      (kappa (meanLowerRoot 12988 θ ^ 2 / gPlus 12988) - 2 / (12988 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12988 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12988)
    linarith
  have ht : √(12 * gPlus 12988) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12988 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12988 12988 (11 / 1000) / √12988 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12988)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12988 (gMinus 12988) (gPlus 12988)
      (finiteEnergy 12988 12988 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12988) (hτ : 0 < (paperDesignP 12988).tau0 c) :
    eR c = (2 / (mA 12988 : ℝ)) *
      normSq (BstLean.Part150.bT 12988 12988 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12988).tau0 c)) /
      (2 / (12988 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12988).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12988).tau0 c))⁻¹ •
      BstLean.Part150.bT 12988 12988 (A1 c) (A2 c) c.1.2 ((paperDesignP 12988).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12988 : ℝ)) * normSq (bR c) / (2 / (12988 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12988}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12988) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12988).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12988 : ℝ) * (paperDesignP 12988).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12988 12988 c.1.2 ((paperDesignP 12988).tau0 c) :=
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

end BstLean.Part266.Row12988

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12989 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12989).real (BstLean.Part211.CentreSource 12989 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12989) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12989 160 (6 / 1000)
  have hj := jS_160_le (n := 12989) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12989 160 (6 / 1000) ^ 2 * 12989 /
      (((12989 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12989 160 (6 / 1000) ^ 2 * 12989 /
      (((12989 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12989 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12989 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12989) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12989 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12989

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12989) :=
  Ethm (paperCentres 12989) ∩ Ethp (paperCentres 12989)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12989)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12989)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12989) (paperCentres 12989)
  have he : exp (-(45 / 10000 * (12989 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12989 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12989) :=
  (passEvent ∩ agentEv (paperDesignP 12989) (DirectionError 12989) ∩
    agentEv (paperDesignP 12989) (CentreSources 12989 12989)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12989)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12989) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12989) hτ
  have hC := centreSources_ret_charge_row 12989 (paperDesignP 12989) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12989)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12989) (CentreSources 12989 12989)
  direction : analyticBase ⊆ agentEv (paperDesignP 12989) (DirectionError 12989)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12989)) : Set (Ret 12989) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12989)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12989)}
    (hT : (retDist (paperCentres 12989)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12989)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12989)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12989)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12989)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12989)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12989

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12989 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12989 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12989 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12989 12989 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12989)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12989)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12989
  have hb0 := BstLean.Part150.betaJ_nonneg 12989
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12989 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12989 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12989 * BstLean.Part150.betaJ 12989) * 12989) ≤
      (81031009 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12989)) * 12989 := by gcongr <;> linarith
      _ ≤ ((81031009 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12989 * 12989 *
      (1 + BstLean.Part154.deltaChi 12989 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92749839 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12989 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92749839 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12989 : ℝ) / BstLean.Part154.csC) ≤ (100142347 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12989 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100142347 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12989 : ℝ) * (81031009 / 500000) +
        2 * (1792 / 10000 / 12989) * (92749839 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100142347 / 1000000) *
          (81 / 1000 / 12989 + (1792 / 10000 / 12989) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12989

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12989
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12989 ∧
    1 ≤ gPlus 12989 ∧ gPlus 12989 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12989 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12989 : ℝ) < √(1 - 2 / (12989 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12989 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12989 (gMinus 12989) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12989 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12989 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12989 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12989)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12989 (gMinus 12989) (gPlus 12989)
      (finiteEnergy 12989 12989 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12989 (gMinus 12989) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12989 (gMinus 12989) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12989 (gMinus 12989) (54 / 100))
    (by linarith : energyRatio 12989 (gMinus 12989) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12989 (gMinus 12989) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12989 * kappa (energyRatio 12989 (gMinus 12989) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12989) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12989 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12989 12989 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12989 12989 (11 / 1000) / √12989 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12989)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12989 * kappa (energyRatio 12989 (gMinus 12989) (54 / 100))) +
      2 * √(12 * gPlus 12989) / 12989 + finiteEnergy 12989 12989 (11 / 1000) / √12989 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12989 θ ∧ meanLowerRoot 12989 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12989 - 2 / (12989 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12989 - 2 / (12989 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12989 θ ^ 2 / gPlus 12989) - 2 / (12989 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12989 * (kappa (meanLowerRoot 12989 θ ^ 2 / gPlus 12989) -
        2 / (12989 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12989) / 12989 -
        finiteEnergy 12989 12989 (11 / 1000) / √12989 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12989 θ ^ 2 / gPlus 12989 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12989)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12989 θ ^ 2 / gPlus 12989 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12989)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12989 θ ^ 2 / gPlus 12989 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12989 ^ 2 ≤
      kappa (meanLowerRoot 12989 θ ^ 2 / gPlus 12989) - 2 / (12989 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12989 *
      (kappa (meanLowerRoot 12989 θ ^ 2 / gPlus 12989) - 2 / (12989 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12989 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12989)
    linarith
  have ht : √(12 * gPlus 12989) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12989 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12989 12989 (11 / 1000) / √12989 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12989)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12989 (gMinus 12989) (gPlus 12989)
      (finiteEnergy 12989 12989 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12989) (hτ : 0 < (paperDesignP 12989).tau0 c) :
    eR c = (2 / (mA 12989 : ℝ)) *
      normSq (BstLean.Part150.bT 12989 12989 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12989).tau0 c)) /
      (2 / (12989 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12989).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12989).tau0 c))⁻¹ •
      BstLean.Part150.bT 12989 12989 (A1 c) (A2 c) c.1.2 ((paperDesignP 12989).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12989 : ℝ)) * normSq (bR c) / (2 / (12989 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12989}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12989) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12989).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12989 : ℝ) * (paperDesignP 12989).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12989 12989 c.1.2 ((paperDesignP 12989).tau0 c) :=
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

end BstLean.Part266.Row12989

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12990 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12990).real (BstLean.Part211.CentreSource 12990 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12990) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12990 160 (6 / 1000)
  have hj := jS_160_le (n := 12990) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12990 160 (6 / 1000) ^ 2 * 12990 /
      (((12990 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12990 160 (6 / 1000) ^ 2 * 12990 /
      (((12990 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12990 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12990 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12990) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12990 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12990

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12990) :=
  Ethm (paperCentres 12990) ∩ Ethp (paperCentres 12990)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12990)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12990)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12990) (paperCentres 12990)
  have he : exp (-(45 / 10000 * (12990 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12990 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12990) :=
  (passEvent ∩ agentEv (paperDesignP 12990) (DirectionError 12990) ∩
    agentEv (paperDesignP 12990) (CentreSources 12990 12990)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12990)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12990) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12990) hτ
  have hC := centreSources_ret_charge_row 12990 (paperDesignP 12990) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12990)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12990) (CentreSources 12990 12990)
  direction : analyticBase ⊆ agentEv (paperDesignP 12990) (DirectionError 12990)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12990)) : Set (Ret 12990) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12990)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12990)}
    (hT : (retDist (paperCentres 12990)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12990)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12990)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12990)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12990)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12990)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12990

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12990 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12990 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12990 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12990 12990 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12990)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12990)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12990
  have hb0 := BstLean.Part150.betaJ_nonneg 12990
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12990 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12990 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12990 * BstLean.Part150.betaJ 12990) * 12990) ≤
      (5064633 / 31250) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12990)) * 12990 := by gcongr <;> linarith
      _ ≤ ((5064633 / 31250) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12990 * 12990 *
      (1 + BstLean.Part154.deltaChi 12990 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92753409 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12990 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92753409 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12990 : ℝ) / BstLean.Part154.csC) ≤ (50073101 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12990 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50073101 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12990 : ℝ) * (5064633 / 31250) +
        2 * (1792 / 10000 / 12990) * (92753409 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (50073101 / 500000) *
          (81 / 1000 / 12990 + (1792 / 10000 / 12990) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12990

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12990
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12990 ∧
    1 ≤ gPlus 12990 ∧ gPlus 12990 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12990 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12990 : ℝ) < √(1 - 2 / (12990 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12990 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12990 (gMinus 12990) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12990 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12990 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12990 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12990)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12990 (gMinus 12990) (gPlus 12990)
      (finiteEnergy 12990 12990 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12990 (gMinus 12990) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12990 (gMinus 12990) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12990 (gMinus 12990) (54 / 100))
    (by linarith : energyRatio 12990 (gMinus 12990) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12990 (gMinus 12990) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12990 * kappa (energyRatio 12990 (gMinus 12990) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12990) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12990 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12990 12990 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12990 12990 (11 / 1000) / √12990 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12990)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12990 * kappa (energyRatio 12990 (gMinus 12990) (54 / 100))) +
      2 * √(12 * gPlus 12990) / 12990 + finiteEnergy 12990 12990 (11 / 1000) / √12990 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12990 θ ∧ meanLowerRoot 12990 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12990 - 2 / (12990 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12990 - 2 / (12990 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12990 θ ^ 2 / gPlus 12990) - 2 / (12990 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12990 * (kappa (meanLowerRoot 12990 θ ^ 2 / gPlus 12990) -
        2 / (12990 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12990) / 12990 -
        finiteEnergy 12990 12990 (11 / 1000) / √12990 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12990 θ ^ 2 / gPlus 12990 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12990)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12990 θ ^ 2 / gPlus 12990 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12990)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12990 θ ^ 2 / gPlus 12990 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12990 ^ 2 ≤
      kappa (meanLowerRoot 12990 θ ^ 2 / gPlus 12990) - 2 / (12990 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12990 *
      (kappa (meanLowerRoot 12990 θ ^ 2 / gPlus 12990) - 2 / (12990 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12990 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12990)
    linarith
  have ht : √(12 * gPlus 12990) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12990 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12990 12990 (11 / 1000) / √12990 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12990)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12990 (gMinus 12990) (gPlus 12990)
      (finiteEnergy 12990 12990 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12990) (hτ : 0 < (paperDesignP 12990).tau0 c) :
    eR c = (2 / (mA 12990 : ℝ)) *
      normSq (BstLean.Part150.bT 12990 12990 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12990).tau0 c)) /
      (2 / (12990 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12990).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12990).tau0 c))⁻¹ •
      BstLean.Part150.bT 12990 12990 (A1 c) (A2 c) c.1.2 ((paperDesignP 12990).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12990 : ℝ)) * normSq (bR c) / (2 / (12990 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12990}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12990) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12990).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12990 : ℝ) * (paperDesignP 12990).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12990 12990 c.1.2 ((paperDesignP 12990).tau0 c) :=
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

end BstLean.Part266.Row12990

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12991 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12991).real (BstLean.Part211.CentreSource 12991 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12991) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12991 160 (6 / 1000)
  have hj := jS_160_le (n := 12991) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12991 160 (6 / 1000) ^ 2 * 12991 /
      (((12991 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12991 160 (6 / 1000) ^ 2 * 12991 /
      (((12991 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12991 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12991 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12991) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12991 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12991

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12991) :=
  Ethm (paperCentres 12991) ∩ Ethp (paperCentres 12991)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12991)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12991)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12991) (paperCentres 12991)
  have he : exp (-(45 / 10000 * (12991 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12991 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12991) :=
  (passEvent ∩ agentEv (paperDesignP 12991) (DirectionError 12991) ∩
    agentEv (paperDesignP 12991) (CentreSources 12991 12991)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12991)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12991) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12991) hτ
  have hC := centreSources_ret_charge_row 12991 (paperDesignP 12991) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12991)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12991) (CentreSources 12991 12991)
  direction : analyticBase ⊆ agentEv (paperDesignP 12991) (DirectionError 12991)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12991)) : Set (Ret 12991) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12991)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12991)}
    (hT : (retDist (paperCentres 12991)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12991)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12991)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12991)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12991)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12991)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12991

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12991 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12991 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12991 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12991 12991 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12991)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12991)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12991
  have hb0 := BstLean.Part150.betaJ_nonneg 12991
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12991 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12991 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12991 * BstLean.Part150.betaJ 12991) * 12991) ≤
      (81037247 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12991)) * 12991 := by gcongr <;> linarith
      _ ≤ ((81037247 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12991 * 12991 *
      (1 + BstLean.Part154.deltaChi 12991 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92756979 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12991 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92756979 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12991 : ℝ) / BstLean.Part154.csC) ≤ (100150057 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12991 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100150057 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12991 : ℝ) * (81037247 / 500000) +
        2 * (1792 / 10000 / 12991) * (92756979 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100150057 / 1000000) *
          (81 / 1000 / 12991 + (1792 / 10000 / 12991) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12991

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12991
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12991 ∧
    1 ≤ gPlus 12991 ∧ gPlus 12991 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12991 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12991 : ℝ) < √(1 - 2 / (12991 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12991 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12991 (gMinus 12991) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12991 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12991 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12991 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12991)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12991 (gMinus 12991) (gPlus 12991)
      (finiteEnergy 12991 12991 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12991 (gMinus 12991) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12991 (gMinus 12991) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12991 (gMinus 12991) (54 / 100))
    (by linarith : energyRatio 12991 (gMinus 12991) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12991 (gMinus 12991) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12991 * kappa (energyRatio 12991 (gMinus 12991) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12991) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12991 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12991 12991 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12991 12991 (11 / 1000) / √12991 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12991)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12991 * kappa (energyRatio 12991 (gMinus 12991) (54 / 100))) +
      2 * √(12 * gPlus 12991) / 12991 + finiteEnergy 12991 12991 (11 / 1000) / √12991 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12991 θ ∧ meanLowerRoot 12991 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12991 - 2 / (12991 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12991 - 2 / (12991 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12991 θ ^ 2 / gPlus 12991) - 2 / (12991 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12991 * (kappa (meanLowerRoot 12991 θ ^ 2 / gPlus 12991) -
        2 / (12991 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12991) / 12991 -
        finiteEnergy 12991 12991 (11 / 1000) / √12991 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12991 θ ^ 2 / gPlus 12991 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12991)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12991 θ ^ 2 / gPlus 12991 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12991)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12991 θ ^ 2 / gPlus 12991 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12991 ^ 2 ≤
      kappa (meanLowerRoot 12991 θ ^ 2 / gPlus 12991) - 2 / (12991 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12991 *
      (kappa (meanLowerRoot 12991 θ ^ 2 / gPlus 12991) - 2 / (12991 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12991 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12991)
    linarith
  have ht : √(12 * gPlus 12991) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12991 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12991 12991 (11 / 1000) / √12991 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12991)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12991 (gMinus 12991) (gPlus 12991)
      (finiteEnergy 12991 12991 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12991) (hτ : 0 < (paperDesignP 12991).tau0 c) :
    eR c = (2 / (mA 12991 : ℝ)) *
      normSq (BstLean.Part150.bT 12991 12991 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12991).tau0 c)) /
      (2 / (12991 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12991).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12991).tau0 c))⁻¹ •
      BstLean.Part150.bT 12991 12991 (A1 c) (A2 c) c.1.2 ((paperDesignP 12991).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12991 : ℝ)) * normSq (bR c) / (2 / (12991 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12991}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12991) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12991).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12991 : ℝ) * (paperDesignP 12991).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12991 12991 c.1.2 ((paperDesignP 12991).tau0 c) :=
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

end BstLean.Part266.Row12991

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12992 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12992).real (BstLean.Part211.CentreSource 12992 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12992) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12992 160 (6 / 1000)
  have hj := jS_160_le (n := 12992) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12992 160 (6 / 1000) ^ 2 * 12992 /
      (((12992 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12992 160 (6 / 1000) ^ 2 * 12992 /
      (((12992 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12992 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12992 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12992) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12992 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12992

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12992) :=
  Ethm (paperCentres 12992) ∩ Ethp (paperCentres 12992)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12992)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12992)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12992) (paperCentres 12992)
  have he : exp (-(45 / 10000 * (12992 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12992 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12992) :=
  (passEvent ∩ agentEv (paperDesignP 12992) (DirectionError 12992) ∩
    agentEv (paperDesignP 12992) (CentreSources 12992 12992)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12992)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12992) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12992) hτ
  have hC := centreSources_ret_charge_row 12992 (paperDesignP 12992) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12992)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12992) (CentreSources 12992 12992)
  direction : analyticBase ⊆ agentEv (paperDesignP 12992) (DirectionError 12992)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12992)) : Set (Ret 12992) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12992)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12992)}
    (hT : (retDist (paperCentres 12992)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12992)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12992)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12992)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12992)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12992)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12992

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12992 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12992 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12992 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12992 12992 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12992)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12992)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12992
  have hb0 := BstLean.Part150.betaJ_nonneg 12992
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12992 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12992 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12992 * BstLean.Part150.betaJ 12992) * 12992) ≤
      (40520183 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12992)) * 12992 := by gcongr <;> linarith
      _ ≤ ((40520183 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12992 * 12992 *
      (1 + BstLean.Part154.deltaChi 12992 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92760549 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12992 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92760549 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12992 : ℝ) / BstLean.Part154.csC) ≤ (100153911 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12992 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100153911 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12992 : ℝ) * (40520183 / 250000) +
        2 * (1792 / 10000 / 12992) * (92760549 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (100153911 / 1000000) *
          (81 / 1000 / 12992 + (1792 / 10000 / 12992) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12992

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12992
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12992 ∧
    1 ≤ gPlus 12992 ∧ gPlus 12992 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12992 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12992 : ℝ) < √(1 - 2 / (12992 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12992 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12992 (gMinus 12992) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12992 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12992 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12992 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12992)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12992 (gMinus 12992) (gPlus 12992)
      (finiteEnergy 12992 12992 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12992 (gMinus 12992) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12992 (gMinus 12992) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12992 (gMinus 12992) (54 / 100))
    (by linarith : energyRatio 12992 (gMinus 12992) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12992 (gMinus 12992) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12992 * kappa (energyRatio 12992 (gMinus 12992) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12992) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12992 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12992 12992 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12992 12992 (11 / 1000) / √12992 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12992)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12992 * kappa (energyRatio 12992 (gMinus 12992) (54 / 100))) +
      2 * √(12 * gPlus 12992) / 12992 + finiteEnergy 12992 12992 (11 / 1000) / √12992 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12992 θ ∧ meanLowerRoot 12992 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12992 - 2 / (12992 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12992 - 2 / (12992 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12992 θ ^ 2 / gPlus 12992) - 2 / (12992 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12992 * (kappa (meanLowerRoot 12992 θ ^ 2 / gPlus 12992) -
        2 / (12992 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12992) / 12992 -
        finiteEnergy 12992 12992 (11 / 1000) / √12992 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12992 θ ^ 2 / gPlus 12992 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12992)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12992 θ ^ 2 / gPlus 12992 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12992)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12992 θ ^ 2 / gPlus 12992 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12992 ^ 2 ≤
      kappa (meanLowerRoot 12992 θ ^ 2 / gPlus 12992) - 2 / (12992 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12992 *
      (kappa (meanLowerRoot 12992 θ ^ 2 / gPlus 12992) - 2 / (12992 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12992 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12992)
    linarith
  have ht : √(12 * gPlus 12992) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12992 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12992 12992 (11 / 1000) / √12992 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12992)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12992 (gMinus 12992) (gPlus 12992)
      (finiteEnergy 12992 12992 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12992) (hτ : 0 < (paperDesignP 12992).tau0 c) :
    eR c = (2 / (mA 12992 : ℝ)) *
      normSq (BstLean.Part150.bT 12992 12992 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12992).tau0 c)) /
      (2 / (12992 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12992).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12992).tau0 c))⁻¹ •
      BstLean.Part150.bT 12992 12992 (A1 c) (A2 c) c.1.2 ((paperDesignP 12992).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12992 : ℝ)) * normSq (bR c) / (2 / (12992 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12992}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12992) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12992).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12992 : ℝ) * (paperDesignP 12992).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12992 12992 c.1.2 ((paperDesignP 12992).tau0 c) :=
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

end BstLean.Part266.Row12992

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12993 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12993).real (BstLean.Part211.CentreSource 12993 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12993) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12993 160 (6 / 1000)
  have hj := jS_160_le (n := 12993) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12993 160 (6 / 1000) ^ 2 * 12993 /
      (((12993 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12993 160 (6 / 1000) ^ 2 * 12993 /
      (((12993 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12993 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12993 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12993) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12993 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12993

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12993) :=
  Ethm (paperCentres 12993) ∩ Ethp (paperCentres 12993)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12993)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12993)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12993) (paperCentres 12993)
  have he : exp (-(45 / 10000 * (12993 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12993 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12993) :=
  (passEvent ∩ agentEv (paperDesignP 12993) (DirectionError 12993) ∩
    agentEv (paperDesignP 12993) (CentreSources 12993 12993)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12993)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12993) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12993) hτ
  have hC := centreSources_ret_charge_row 12993 (paperDesignP 12993) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12993)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12993) (CentreSources 12993 12993)
  direction : analyticBase ⊆ agentEv (paperDesignP 12993) (DirectionError 12993)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12993)) : Set (Ret 12993) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12993)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12993)}
    (hT : (retDist (paperCentres 12993)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12993)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12993)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12993)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12993)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12993)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12993

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12993 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12993 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12993 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12993 12993 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12993)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12993)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12993
  have hb0 := BstLean.Part150.betaJ_nonneg 12993
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12993 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12993 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12993 * BstLean.Part150.betaJ 12993) * 12993) ≤
      (16208697 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12993)) * 12993 := by gcongr <;> linarith
      _ ≤ ((16208697 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12993 * 12993 *
      (1 + BstLean.Part154.deltaChi 12993 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92764119 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12993 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92764119 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12993 : ℝ) / BstLean.Part154.csC) ≤ (50078883 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12993 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50078883 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12993 : ℝ) * (16208697 / 100000) +
        2 * (1792 / 10000 / 12993) * (92764119 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (50078883 / 500000) *
          (81 / 1000 / 12993 + (1792 / 10000 / 12993) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12993

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12993
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12993 ∧
    1 ≤ gPlus 12993 ∧ gPlus 12993 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12993 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12993 : ℝ) < √(1 - 2 / (12993 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12993 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12993 (gMinus 12993) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12993 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12993 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12993 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12993)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12993 (gMinus 12993) (gPlus 12993)
      (finiteEnergy 12993 12993 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12993 (gMinus 12993) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12993 (gMinus 12993) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12993 (gMinus 12993) (54 / 100))
    (by linarith : energyRatio 12993 (gMinus 12993) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12993 (gMinus 12993) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12993 * kappa (energyRatio 12993 (gMinus 12993) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12993) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12993 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12993 12993 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12993 12993 (11 / 1000) / √12993 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12993)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12993 * kappa (energyRatio 12993 (gMinus 12993) (54 / 100))) +
      2 * √(12 * gPlus 12993) / 12993 + finiteEnergy 12993 12993 (11 / 1000) / √12993 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12993 θ ∧ meanLowerRoot 12993 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12993 - 2 / (12993 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12993 - 2 / (12993 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12993 θ ^ 2 / gPlus 12993) - 2 / (12993 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12993 * (kappa (meanLowerRoot 12993 θ ^ 2 / gPlus 12993) -
        2 / (12993 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12993) / 12993 -
        finiteEnergy 12993 12993 (11 / 1000) / √12993 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12993 θ ^ 2 / gPlus 12993 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12993)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12993 θ ^ 2 / gPlus 12993 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12993)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12993 θ ^ 2 / gPlus 12993 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12993 ^ 2 ≤
      kappa (meanLowerRoot 12993 θ ^ 2 / gPlus 12993) - 2 / (12993 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12993 *
      (kappa (meanLowerRoot 12993 θ ^ 2 / gPlus 12993) - 2 / (12993 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12993 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12993)
    linarith
  have ht : √(12 * gPlus 12993) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12993 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12993 12993 (11 / 1000) / √12993 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12993)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12993 (gMinus 12993) (gPlus 12993)
      (finiteEnergy 12993 12993 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12993) (hτ : 0 < (paperDesignP 12993).tau0 c) :
    eR c = (2 / (mA 12993 : ℝ)) *
      normSq (BstLean.Part150.bT 12993 12993 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12993).tau0 c)) /
      (2 / (12993 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12993).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12993).tau0 c))⁻¹ •
      BstLean.Part150.bT 12993 12993 (A1 c) (A2 c) c.1.2 ((paperDesignP 12993).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12993 : ℝ)) * normSq (bR c) / (2 / (12993 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12993}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12993) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12993).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12993 : ℝ) * (paperDesignP 12993).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12993 12993 c.1.2 ((paperDesignP 12993).tau0 c) :=
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

end BstLean.Part266.Row12993

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12994 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12994).real (BstLean.Part211.CentreSource 12994 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12994) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12994 160 (6 / 1000)
  have hj := jS_160_le (n := 12994) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12994 160 (6 / 1000) ^ 2 * 12994 /
      (((12994 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12994 160 (6 / 1000) ^ 2 * 12994 /
      (((12994 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12994 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12994 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12994) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12994 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12994

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12994) :=
  Ethm (paperCentres 12994) ∩ Ethp (paperCentres 12994)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12994)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12994)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12994) (paperCentres 12994)
  have he : exp (-(45 / 10000 * (12994 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12994 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12994) :=
  (passEvent ∩ agentEv (paperDesignP 12994) (DirectionError 12994) ∩
    agentEv (paperDesignP 12994) (CentreSources 12994 12994)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12994)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12994) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12994) hτ
  have hC := centreSources_ret_charge_row 12994 (paperDesignP 12994) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12994)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12994) (CentreSources 12994 12994)
  direction : analyticBase ⊆ agentEv (paperDesignP 12994) (DirectionError 12994)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12994)) : Set (Ret 12994) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12994)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12994)}
    (hT : (retDist (paperCentres 12994)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12994)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12994)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12994)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12994)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12994)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12994

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12994 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12994 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12994 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12994 12994 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12994)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12994)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12994
  have hb0 := BstLean.Part150.betaJ_nonneg 12994
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12994 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12994 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12994 * BstLean.Part150.betaJ 12994) * 12994) ≤
      (162093207 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12994)) * 12994 := by gcongr <;> linarith
      _ ≤ ((162093207 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12994 * 12994 *
      (1 + BstLean.Part154.deltaChi 12994 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185535377 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12994 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185535377 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12994 : ℝ) / BstLean.Part154.csC) ≤ (5008081 / 50000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12994 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((5008081 / 50000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12994 : ℝ) * (162093207 / 1000000) +
        2 * (1792 / 10000 / 12994) * (185535377 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (5008081 / 50000) *
          (81 / 1000 / 12994 + (1792 / 10000 / 12994) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12994

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12994
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12994 ∧
    1 ≤ gPlus 12994 ∧ gPlus 12994 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12994 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12994 : ℝ) < √(1 - 2 / (12994 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12994 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12994 (gMinus 12994) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12994 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12994 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12994 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12994)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12994 (gMinus 12994) (gPlus 12994)
      (finiteEnergy 12994 12994 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12994 (gMinus 12994) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12994 (gMinus 12994) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12994 (gMinus 12994) (54 / 100))
    (by linarith : energyRatio 12994 (gMinus 12994) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12994 (gMinus 12994) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12994 * kappa (energyRatio 12994 (gMinus 12994) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12994) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12994 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12994 12994 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12994 12994 (11 / 1000) / √12994 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12994)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12994 * kappa (energyRatio 12994 (gMinus 12994) (54 / 100))) +
      2 * √(12 * gPlus 12994) / 12994 + finiteEnergy 12994 12994 (11 / 1000) / √12994 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12994 θ ∧ meanLowerRoot 12994 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12994 - 2 / (12994 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12994 - 2 / (12994 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12994 θ ^ 2 / gPlus 12994) - 2 / (12994 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12994 * (kappa (meanLowerRoot 12994 θ ^ 2 / gPlus 12994) -
        2 / (12994 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12994) / 12994 -
        finiteEnergy 12994 12994 (11 / 1000) / √12994 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12994 θ ^ 2 / gPlus 12994 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12994)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12994 θ ^ 2 / gPlus 12994 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12994)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12994 θ ^ 2 / gPlus 12994 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12994 ^ 2 ≤
      kappa (meanLowerRoot 12994 θ ^ 2 / gPlus 12994) - 2 / (12994 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12994 *
      (kappa (meanLowerRoot 12994 θ ^ 2 / gPlus 12994) - 2 / (12994 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12994 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12994)
    linarith
  have ht : √(12 * gPlus 12994) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12994 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12994 12994 (11 / 1000) / √12994 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12994)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12994 (gMinus 12994) (gPlus 12994)
      (finiteEnergy 12994 12994 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12994) (hτ : 0 < (paperDesignP 12994).tau0 c) :
    eR c = (2 / (mA 12994 : ℝ)) *
      normSq (BstLean.Part150.bT 12994 12994 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12994).tau0 c)) /
      (2 / (12994 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12994).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12994).tau0 c))⁻¹ •
      BstLean.Part150.bT 12994 12994 (A1 c) (A2 c) c.1.2 ((paperDesignP 12994).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12994 : ℝ)) * normSq (bR c) / (2 / (12994 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12994}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12994) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12994).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12994 : ℝ) * (paperDesignP 12994).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12994 12994 c.1.2 ((paperDesignP 12994).tau0 c) :=
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

end BstLean.Part266.Row12994

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12995 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12995).real (BstLean.Part211.CentreSource 12995 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12995) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12995 160 (6 / 1000)
  have hj := jS_160_le (n := 12995) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12995 160 (6 / 1000) ^ 2 * 12995 /
      (((12995 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12995 160 (6 / 1000) ^ 2 * 12995 /
      (((12995 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12995 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12995 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12995) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12995 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12995

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12995) :=
  Ethm (paperCentres 12995) ∩ Ethp (paperCentres 12995)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12995)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12995)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12995) (paperCentres 12995)
  have he : exp (-(45 / 10000 * (12995 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12995 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12995) :=
  (passEvent ∩ agentEv (paperDesignP 12995) (DirectionError 12995) ∩
    agentEv (paperDesignP 12995) (CentreSources 12995 12995)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12995)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12995) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12995) hτ
  have hC := centreSources_ret_charge_row 12995 (paperDesignP 12995) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12995)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12995) (CentreSources 12995 12995)
  direction : analyticBase ⊆ agentEv (paperDesignP 12995) (DirectionError 12995)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12995)) : Set (Ret 12995) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12995)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12995)}
    (hT : (retDist (paperCentres 12995)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12995)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12995)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12995)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12995)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12995)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12995

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12995 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12995 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12995 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12995 12995 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12995)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12995)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12995
  have hb0 := BstLean.Part150.betaJ_nonneg 12995
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12995 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12995 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12995 * BstLean.Part150.betaJ 12995) * 12995) ≤
      (40524861 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12995)) * 12995 := by gcongr <;> linarith
      _ ≤ ((40524861 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12995 * 12995 *
      (1 + BstLean.Part154.deltaChi 12995 12 + 2 / π) / BstLean.Part154.csC) ≤
      (185542517 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12995 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((185542517 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12995 : ℝ) / BstLean.Part154.csC) ≤ (50082737 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12995 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50082737 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12995 : ℝ) * (40524861 / 250000) +
        2 * (1792 / 10000 / 12995) * (185542517 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (50082737 / 500000) *
          (81 / 1000 / 12995 + (1792 / 10000 / 12995) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12995

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12995
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12995 ∧
    1 ≤ gPlus 12995 ∧ gPlus 12995 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12995 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12995 : ℝ) < √(1 - 2 / (12995 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12995 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12995 (gMinus 12995) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12995 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12995 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12995 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12995)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12995 (gMinus 12995) (gPlus 12995)
      (finiteEnergy 12995 12995 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12995 (gMinus 12995) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12995 (gMinus 12995) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12995 (gMinus 12995) (54 / 100))
    (by linarith : energyRatio 12995 (gMinus 12995) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12995 (gMinus 12995) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12995 * kappa (energyRatio 12995 (gMinus 12995) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12995) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12995 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12995 12995 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12995 12995 (11 / 1000) / √12995 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12995)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12995 * kappa (energyRatio 12995 (gMinus 12995) (54 / 100))) +
      2 * √(12 * gPlus 12995) / 12995 + finiteEnergy 12995 12995 (11 / 1000) / √12995 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12995 θ ∧ meanLowerRoot 12995 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12995 - 2 / (12995 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12995 - 2 / (12995 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12995 θ ^ 2 / gPlus 12995) - 2 / (12995 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12995 * (kappa (meanLowerRoot 12995 θ ^ 2 / gPlus 12995) -
        2 / (12995 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12995) / 12995 -
        finiteEnergy 12995 12995 (11 / 1000) / √12995 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12995 θ ^ 2 / gPlus 12995 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12995)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12995 θ ^ 2 / gPlus 12995 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12995)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12995 θ ^ 2 / gPlus 12995 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12995 ^ 2 ≤
      kappa (meanLowerRoot 12995 θ ^ 2 / gPlus 12995) - 2 / (12995 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12995 *
      (kappa (meanLowerRoot 12995 θ ^ 2 / gPlus 12995) - 2 / (12995 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12995 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12995)
    linarith
  have ht : √(12 * gPlus 12995) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12995 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12995 12995 (11 / 1000) / √12995 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12995)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12995 (gMinus 12995) (gPlus 12995)
      (finiteEnergy 12995 12995 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12995) (hτ : 0 < (paperDesignP 12995).tau0 c) :
    eR c = (2 / (mA 12995 : ℝ)) *
      normSq (BstLean.Part150.bT 12995 12995 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12995).tau0 c)) /
      (2 / (12995 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12995).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12995).tau0 c))⁻¹ •
      BstLean.Part150.bT 12995 12995 (A1 c) (A2 c) c.1.2 ((paperDesignP 12995).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12995 : ℝ)) * normSq (bR c) / (2 / (12995 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12995}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12995) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12995).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12995 : ℝ) * (paperDesignP 12995).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12995 12995 c.1.2 ((paperDesignP 12995).tau0 c) :=
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

end BstLean.Part266.Row12995

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12996 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12996).real (BstLean.Part211.CentreSource 12996 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12996) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12996 160 (6 / 1000)
  have hj := jS_160_le (n := 12996) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12996 160 (6 / 1000) ^ 2 * 12996 /
      (((12996 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12996 160 (6 / 1000) ^ 2 * 12996 /
      (((12996 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12996 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12996 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12996) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12996 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12996

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12996) :=
  Ethm (paperCentres 12996) ∩ Ethp (paperCentres 12996)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12996)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12996)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12996) (paperCentres 12996)
  have he : exp (-(45 / 10000 * (12996 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12996 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12996) :=
  (passEvent ∩ agentEv (paperDesignP 12996) (DirectionError 12996) ∩
    agentEv (paperDesignP 12996) (CentreSources 12996 12996)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12996)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12996) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12996) hτ
  have hC := centreSources_ret_charge_row 12996 (paperDesignP 12996) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12996)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12996) (CentreSources 12996 12996)
  direction : analyticBase ⊆ agentEv (paperDesignP 12996) (DirectionError 12996)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12996)) : Set (Ret 12996) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12996)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12996)}
    (hT : (retDist (paperCentres 12996)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12996)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12996)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12996)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12996)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12996)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12996

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12996 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12996 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12996 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12996 12996 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12996)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12996)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12996
  have hb0 := BstLean.Part150.betaJ_nonneg 12996
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12996 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12996 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12996 * BstLean.Part150.betaJ 12996) * 12996) ≤
      (162105681 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12996)) * 12996 := by gcongr <;> linarith
      _ ≤ ((162105681 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12996 * 12996 *
      (1 + BstLean.Part154.deltaChi 12996 12 + 2 / π) / BstLean.Part154.csC) ≤
      (37109931 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12996 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((37109931 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12996 : ℝ) / BstLean.Part154.csC) ≤ (6260583 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12996 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((6260583 / 62500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12996 : ℝ) * (162105681 / 1000000) +
        2 * (1792 / 10000 / 12996) * (37109931 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (6260583 / 62500) *
          (81 / 1000 / 12996 + (1792 / 10000 / 12996) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12996

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12996
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12996 ∧
    1 ≤ gPlus 12996 ∧ gPlus 12996 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12996 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12996 : ℝ) < √(1 - 2 / (12996 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12996 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12996 (gMinus 12996) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12996 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12996 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12996 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12996)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12996 (gMinus 12996) (gPlus 12996)
      (finiteEnergy 12996 12996 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12996 (gMinus 12996) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12996 (gMinus 12996) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12996 (gMinus 12996) (54 / 100))
    (by linarith : energyRatio 12996 (gMinus 12996) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12996 (gMinus 12996) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12996 * kappa (energyRatio 12996 (gMinus 12996) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12996) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12996 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12996 12996 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12996 12996 (11 / 1000) / √12996 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12996)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12996 * kappa (energyRatio 12996 (gMinus 12996) (54 / 100))) +
      2 * √(12 * gPlus 12996) / 12996 + finiteEnergy 12996 12996 (11 / 1000) / √12996 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12996 θ ∧ meanLowerRoot 12996 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12996 - 2 / (12996 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12996 - 2 / (12996 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12996 θ ^ 2 / gPlus 12996) - 2 / (12996 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12996 * (kappa (meanLowerRoot 12996 θ ^ 2 / gPlus 12996) -
        2 / (12996 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12996) / 12996 -
        finiteEnergy 12996 12996 (11 / 1000) / √12996 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12996 θ ^ 2 / gPlus 12996 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12996)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12996 θ ^ 2 / gPlus 12996 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12996)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12996 θ ^ 2 / gPlus 12996 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12996 ^ 2 ≤
      kappa (meanLowerRoot 12996 θ ^ 2 / gPlus 12996) - 2 / (12996 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12996 *
      (kappa (meanLowerRoot 12996 θ ^ 2 / gPlus 12996) - 2 / (12996 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12996 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12996)
    linarith
  have ht : √(12 * gPlus 12996) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12996 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12996 12996 (11 / 1000) / √12996 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12996)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12996 (gMinus 12996) (gPlus 12996)
      (finiteEnergy 12996 12996 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12996) (hτ : 0 < (paperDesignP 12996).tau0 c) :
    eR c = (2 / (mA 12996 : ℝ)) *
      normSq (BstLean.Part150.bT 12996 12996 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12996).tau0 c)) /
      (2 / (12996 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12996).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12996).tau0 c))⁻¹ •
      BstLean.Part150.bT 12996 12996 (A1 c) (A2 c) c.1.2 ((paperDesignP 12996).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12996 : ℝ)) * normSq (bR c) / (2 / (12996 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12996}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12996) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12996).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12996 : ℝ) * (paperDesignP 12996).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12996 12996 c.1.2 ((paperDesignP 12996).tau0 c) :=
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

end BstLean.Part266.Row12996

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12997 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12997).real (BstLean.Part211.CentreSource 12997 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12997) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12997 160 (6 / 1000)
  have hj := jS_160_le (n := 12997) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12997 160 (6 / 1000) ^ 2 * 12997 /
      (((12997 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12997 160 (6 / 1000) ^ 2 * 12997 /
      (((12997 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12997 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12997 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12997) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12997 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12997

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12997) :=
  Ethm (paperCentres 12997) ∩ Ethp (paperCentres 12997)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12997)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12997)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12997) (paperCentres 12997)
  have he : exp (-(45 / 10000 * (12997 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12997 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12997) :=
  (passEvent ∩ agentEv (paperDesignP 12997) (DirectionError 12997) ∩
    agentEv (paperDesignP 12997) (CentreSources 12997 12997)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12997)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12997) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12997) hτ
  have hC := centreSources_ret_charge_row 12997 (paperDesignP 12997) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12997)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12997) (CentreSources 12997 12997)
  direction : analyticBase ⊆ agentEv (paperDesignP 12997) (DirectionError 12997)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12997)) : Set (Ret 12997) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12997)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12997)}
    (hT : (retDist (paperCentres 12997)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12997)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12997)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12997)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12997)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12997)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12997

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12997 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12997 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12997 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12997 12997 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12997)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12997)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12997
  have hb0 := BstLean.Part150.betaJ_nonneg 12997
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12997 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12997 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12997 * BstLean.Part150.betaJ 12997) * 12997) ≤
      (162111917 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12997)) * 12997 := by gcongr <;> linarith
      _ ≤ ((162111917 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12997 * 12997 *
      (1 + BstLean.Part154.deltaChi 12997 12 + 2 / π) / BstLean.Part154.csC) ≤
      (92778397 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12997 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((92778397 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12997 : ℝ) / BstLean.Part154.csC) ≤ (50086591 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12997 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50086591 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12997 : ℝ) * (162111917 / 1000000) +
        2 * (1792 / 10000 / 12997) * (92778397 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (50086591 / 500000) *
          (81 / 1000 / 12997 + (1792 / 10000 / 12997) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12997

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12997
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12997 ∧
    1 ≤ gPlus 12997 ∧ gPlus 12997 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12997 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12997 : ℝ) < √(1 - 2 / (12997 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12997 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12997 (gMinus 12997) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12997 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12997 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12997 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12997)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12997 (gMinus 12997) (gPlus 12997)
      (finiteEnergy 12997 12997 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12997 (gMinus 12997) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12997 (gMinus 12997) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12997 (gMinus 12997) (54 / 100))
    (by linarith : energyRatio 12997 (gMinus 12997) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12997 (gMinus 12997) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12997 * kappa (energyRatio 12997 (gMinus 12997) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12997) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12997 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12997 12997 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12997 12997 (11 / 1000) / √12997 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12997)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12997 * kappa (energyRatio 12997 (gMinus 12997) (54 / 100))) +
      2 * √(12 * gPlus 12997) / 12997 + finiteEnergy 12997 12997 (11 / 1000) / √12997 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12997 θ ∧ meanLowerRoot 12997 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12997 - 2 / (12997 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12997 - 2 / (12997 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12997 θ ^ 2 / gPlus 12997) - 2 / (12997 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12997 * (kappa (meanLowerRoot 12997 θ ^ 2 / gPlus 12997) -
        2 / (12997 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12997) / 12997 -
        finiteEnergy 12997 12997 (11 / 1000) / √12997 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12997 θ ^ 2 / gPlus 12997 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12997)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12997 θ ^ 2 / gPlus 12997 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12997)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12997 θ ^ 2 / gPlus 12997 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12997 ^ 2 ≤
      kappa (meanLowerRoot 12997 θ ^ 2 / gPlus 12997) - 2 / (12997 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12997 *
      (kappa (meanLowerRoot 12997 θ ^ 2 / gPlus 12997) - 2 / (12997 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12997 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12997)
    linarith
  have ht : √(12 * gPlus 12997) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12997 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12997 12997 (11 / 1000) / √12997 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12997)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12997 (gMinus 12997) (gPlus 12997)
      (finiteEnergy 12997 12997 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12997) (hτ : 0 < (paperDesignP 12997).tau0 c) :
    eR c = (2 / (mA 12997 : ℝ)) *
      normSq (BstLean.Part150.bT 12997 12997 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12997).tau0 c)) /
      (2 / (12997 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12997).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12997).tau0 c))⁻¹ •
      BstLean.Part150.bT 12997 12997 (A1 c) (A2 c) c.1.2 ((paperDesignP 12997).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12997 : ℝ)) * normSq (bR c) / (2 / (12997 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12997}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12997) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12997).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12997 : ℝ) * (paperDesignP 12997).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12997 12997 c.1.2 ((paperDesignP 12997).tau0 c) :=
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

end BstLean.Part266.Row12997

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12998 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12998).real (BstLean.Part211.CentreSource 12998 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12998) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12998 160 (6 / 1000)
  have hj := jS_160_le (n := 12998) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12998 160 (6 / 1000) ^ 2 * 12998 /
      (((12998 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12998 160 (6 / 1000) ^ 2 * 12998 /
      (((12998 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12998 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12998 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12998) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12998 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12998

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12998) :=
  Ethm (paperCentres 12998) ∩ Ethp (paperCentres 12998)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12998)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12998)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12998) (paperCentres 12998)
  have he : exp (-(45 / 10000 * (12998 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12998 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12998) :=
  (passEvent ∩ agentEv (paperDesignP 12998) (DirectionError 12998) ∩
    agentEv (paperDesignP 12998) (CentreSources 12998 12998)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12998)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12998) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12998) hτ
  have hC := centreSources_ret_charge_row 12998 (paperDesignP 12998) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12998)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12998) (CentreSources 12998 12998)
  direction : analyticBase ⊆ agentEv (paperDesignP 12998) (DirectionError 12998)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12998)) : Set (Ret 12998) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12998)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12998)}
    (hT : (retDist (paperCentres 12998)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12998)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12998)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12998)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12998)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12998)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12998

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12998 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12998 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12998 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12998 12998 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12998)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12998)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12998
  have hb0 := BstLean.Part150.betaJ_nonneg 12998
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12998 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12998 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12998 * BstLean.Part150.betaJ 12998) * 12998) ≤
      (162118153 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12998)) * 12998 := by gcongr <;> linarith
      _ ≤ ((162118153 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12998 * 12998 *
      (1 + BstLean.Part154.deltaChi 12998 12 + 2 / π) / BstLean.Part154.csC) ≤
      (46390983 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12998 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((46390983 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12998 : ℝ) / BstLean.Part154.csC) ≤ (20035407 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12998 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((20035407 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12998 : ℝ) * (162118153 / 1000000) +
        2 * (1792 / 10000 / 12998) * (46390983 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (20035407 / 200000) *
          (81 / 1000 / 12998 + (1792 / 10000 / 12998) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12998

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12998
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12998 ∧
    1 ≤ gPlus 12998 ∧ gPlus 12998 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12998 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12998 : ℝ) < √(1 - 2 / (12998 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12998 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12998 (gMinus 12998) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12998 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12998 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12998 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12998)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12998 (gMinus 12998) (gPlus 12998)
      (finiteEnergy 12998 12998 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12998 (gMinus 12998) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12998 (gMinus 12998) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12998 (gMinus 12998) (54 / 100))
    (by linarith : energyRatio 12998 (gMinus 12998) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12998 (gMinus 12998) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12998 * kappa (energyRatio 12998 (gMinus 12998) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12998) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12998 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12998 12998 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12998 12998 (11 / 1000) / √12998 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12998)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12998 * kappa (energyRatio 12998 (gMinus 12998) (54 / 100))) +
      2 * √(12 * gPlus 12998) / 12998 + finiteEnergy 12998 12998 (11 / 1000) / √12998 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12998 θ ∧ meanLowerRoot 12998 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12998 - 2 / (12998 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12998 - 2 / (12998 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12998 θ ^ 2 / gPlus 12998) - 2 / (12998 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12998 * (kappa (meanLowerRoot 12998 θ ^ 2 / gPlus 12998) -
        2 / (12998 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12998) / 12998 -
        finiteEnergy 12998 12998 (11 / 1000) / √12998 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12998 θ ^ 2 / gPlus 12998 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12998)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12998 θ ^ 2 / gPlus 12998 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12998)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12998 θ ^ 2 / gPlus 12998 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12998 ^ 2 ≤
      kappa (meanLowerRoot 12998 θ ^ 2 / gPlus 12998) - 2 / (12998 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12998 *
      (kappa (meanLowerRoot 12998 θ ^ 2 / gPlus 12998) - 2 / (12998 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12998 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12998)
    linarith
  have ht : √(12 * gPlus 12998) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12998 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12998 12998 (11 / 1000) / √12998 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12998)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12998 (gMinus 12998) (gPlus 12998)
      (finiteEnergy 12998 12998 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12998) (hτ : 0 < (paperDesignP 12998).tau0 c) :
    eR c = (2 / (mA 12998 : ℝ)) *
      normSq (BstLean.Part150.bT 12998 12998 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12998).tau0 c)) /
      (2 / (12998 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12998).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12998).tau0 c))⁻¹ •
      BstLean.Part150.bT 12998 12998 (A1 c) (A2 c) c.1.2 ((paperDesignP 12998).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12998 : ℝ)) * normSq (bR c) / (2 / (12998 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12998}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12998) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12998).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12998 : ℝ) * (paperDesignP 12998).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12998 12998 c.1.2 ((paperDesignP 12998).tau0 c) :=
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

end BstLean.Part266.Row12998

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12999 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12999).real (BstLean.Part211.CentreSource 12999 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12999) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12999 160 (6 / 1000)
  have hj := jS_160_le (n := 12999) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12999 160 (6 / 1000) ^ 2 * 12999 /
      (((12999 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12999 160 (6 / 1000) ^ 2 * 12999 /
      (((12999 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12999 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12999 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12999) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12999 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12999

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12999) :=
  Ethm (paperCentres 12999) ∩ Ethp (paperCentres 12999)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12999)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12999)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12999) (paperCentres 12999)
  have he : exp (-(45 / 10000 * (12999 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12999 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12999) :=
  (passEvent ∩ agentEv (paperDesignP 12999) (DirectionError 12999) ∩
    agentEv (paperDesignP 12999) (CentreSources 12999 12999)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12999)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12999) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12999) hτ
  have hC := centreSources_ret_charge_row 12999 (paperDesignP 12999) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12999)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12999) (CentreSources 12999 12999)
  direction : analyticBase ⊆ agentEv (paperDesignP 12999) (DirectionError 12999)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12999)) : Set (Ret 12999) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12999)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12999)}
    (hT : (retDist (paperCentres 12999)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12999)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12999)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12999)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12999)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12999)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12999

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12999 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12999 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12999 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12999 12999 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12999)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12999)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12999
  have hb0 := BstLean.Part150.betaJ_nonneg 12999
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12999 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12999 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12999 * BstLean.Part150.betaJ 12999) * 12999) ≤
      (16212439 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12999)) * 12999 := by gcongr <;> linarith
      _ ≤ ((16212439 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12999 * 12999 *
      (1 + BstLean.Part154.deltaChi 12999 12 + 2 / π) / BstLean.Part154.csC) ≤
      (18557107 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12999 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((18557107 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12999 : ℝ) / BstLean.Part154.csC) ≤ (100180889 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12999 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((100180889 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12999 : ℝ) * (16212439 / 100000) +
        2 * (1792 / 10000 / 12999) * (18557107 / 100000) +
        4 * (1 / 2.506628) * 1.036505 * (100180889 / 1000000) *
          (81 / 1000 / 12999 + (1792 / 10000 / 12999) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12999

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12999
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12999 ∧
    1 ≤ gPlus 12999 ∧ gPlus 12999 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12999 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12999 : ℝ) < √(1 - 2 / (12999 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12999 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12999 (gMinus 12999) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12999 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12999 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12999 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12999)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12999 (gMinus 12999) (gPlus 12999)
      (finiteEnergy 12999 12999 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12999 (gMinus 12999) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12999 (gMinus 12999) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12999 (gMinus 12999) (54 / 100))
    (by linarith : energyRatio 12999 (gMinus 12999) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12999 (gMinus 12999) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12999 * kappa (energyRatio 12999 (gMinus 12999) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12999) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12999 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12999 12999 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12999 12999 (11 / 1000) / √12999 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12999)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12999 * kappa (energyRatio 12999 (gMinus 12999) (54 / 100))) +
      2 * √(12 * gPlus 12999) / 12999 + finiteEnergy 12999 12999 (11 / 1000) / √12999 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12999 θ ∧ meanLowerRoot 12999 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12999 - 2 / (12999 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12999 - 2 / (12999 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12999 θ ^ 2 / gPlus 12999) - 2 / (12999 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12999 * (kappa (meanLowerRoot 12999 θ ^ 2 / gPlus 12999) -
        2 / (12999 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12999) / 12999 -
        finiteEnergy 12999 12999 (11 / 1000) / √12999 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12999 θ ^ 2 / gPlus 12999 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12999)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12999 θ ^ 2 / gPlus 12999 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12999)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12999 θ ^ 2 / gPlus 12999 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12999 ^ 2 ≤
      kappa (meanLowerRoot 12999 θ ^ 2 / gPlus 12999) - 2 / (12999 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12999 *
      (kappa (meanLowerRoot 12999 θ ^ 2 / gPlus 12999) - 2 / (12999 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12999 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12999)
    linarith
  have ht : √(12 * gPlus 12999) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12999 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12999 12999 (11 / 1000) / √12999 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12999)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12999 (gMinus 12999) (gPlus 12999)
      (finiteEnergy 12999 12999 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12999) (hτ : 0 < (paperDesignP 12999).tau0 c) :
    eR c = (2 / (mA 12999 : ℝ)) *
      normSq (BstLean.Part150.bT 12999 12999 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12999).tau0 c)) /
      (2 / (12999 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12999).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12999).tau0 c))⁻¹ •
      BstLean.Part150.bT 12999 12999 (A1 c) (A2 c) c.1.2 ((paperDesignP 12999).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12999 : ℝ)) * normSq (bR c) / (2 / (12999 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12999}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12999) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12999).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12999 : ℝ) * (paperDesignP 12999).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12999 12999 c.1.2 ((paperDesignP 12999).tau0 c) :=
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

end BstLean.Part266.Row12999
