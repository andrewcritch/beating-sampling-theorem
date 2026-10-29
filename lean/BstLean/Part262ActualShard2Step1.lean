import BstLean.Part262ActualShard2Step0


/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12275
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12275 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12275).real (BstLean.Part211.CentreSource 12275 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12275) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12275 160 (6 / 1000)
  have hj := jS_160_le (n := 12275) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12275 160 (6 / 1000) ^ 2 * 12275 /
      (((12275 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12275 160 (6 / 1000) ^ 2 * 12275 /
      (((12275 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12275 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12275 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12275) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12275 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12275

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12275
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12275) :=
  Ethm (paperCentres 12275) ∩ Ethp (paperCentres 12275)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12275)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12275)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12275) (paperCentres 12275)
  have he : exp (-(45 / 10000 * (12275 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12275 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12275) :=
  (passEvent ∩ agentEv (paperDesignP 12275) (DirectionError 12275) ∩
    agentEv (paperDesignP 12275) (CentreSources 12275 12275)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12275)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12275) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12275) hτ
  have hC := centreSources_ret_charge_row 12275 (paperDesignP 12275) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12275)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12275) (CentreSources 12275 12275)
  direction : analyticBase ⊆ agentEv (paperDesignP 12275) (DirectionError 12275)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12275)) : Set (Ret 12275) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12275)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12275)}
    (hT : (retDist (paperCentres 12275)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12275)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12275)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12275)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12275)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12275)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12275

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12275
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12275 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12275 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12275 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12275 12275 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12275)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12275)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12275
  have hb0 := BstLean.Part150.betaJ_nonneg 12275
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12275 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12275 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12275 * BstLean.Part150.betaJ 12275) * 12275) ≤
      (157544881 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12275)) * 12275 := by gcongr <;> linarith
      _ ≤ ((157544881 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12275 * 12275 *
      (1 + BstLean.Part154.deltaChi 12275 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90164599 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12275 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90164599 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12275 : ℝ) / BstLean.Part154.csC) ≤ (48675527 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12275 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48675527 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12275 : ℝ) * (157544881 / 1000000) +
        2 * (1792 / 10000 / 12275) * (90164599 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (48675527 / 500000) *
          (81 / 1000 / 12275 + (1792 / 10000 / 12275) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12275

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12275
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12275 ∧
    1 ≤ gPlus 12275 ∧ gPlus 12275 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12275 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12275 : ℝ) < √(1 - 2 / (12275 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12275 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12275 (gMinus 12275) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12275 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12275 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12275 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12275)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12275 (gMinus 12275) (gPlus 12275)
      (finiteEnergy 12275 12275 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12275 (gMinus 12275) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12275 (gMinus 12275) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12275 (gMinus 12275) (54 / 100))
    (by linarith : energyRatio 12275 (gMinus 12275) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12275 (gMinus 12275) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12275 * kappa (energyRatio 12275 (gMinus 12275) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12275) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12275 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12275 12275 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12275 12275 (11 / 1000) / √12275 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12275)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12275 * kappa (energyRatio 12275 (gMinus 12275) (54 / 100))) +
      2 * √(12 * gPlus 12275) / 12275 + finiteEnergy 12275 12275 (11 / 1000) / √12275 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12275 θ ∧ meanLowerRoot 12275 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12275 - 2 / (12275 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12275 - 2 / (12275 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12275 θ ^ 2 / gPlus 12275) - 2 / (12275 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12275 * (kappa (meanLowerRoot 12275 θ ^ 2 / gPlus 12275) -
        2 / (12275 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12275) / 12275 -
        finiteEnergy 12275 12275 (11 / 1000) / √12275 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12275 θ ^ 2 / gPlus 12275 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12275)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12275 θ ^ 2 / gPlus 12275 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12275)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12275 θ ^ 2 / gPlus 12275 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12275 ^ 2 ≤
      kappa (meanLowerRoot 12275 θ ^ 2 / gPlus 12275) - 2 / (12275 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12275 *
      (kappa (meanLowerRoot 12275 θ ^ 2 / gPlus 12275) - 2 / (12275 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12275 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12275)
    linarith
  have ht : √(12 * gPlus 12275) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12275 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12275 12275 (11 / 1000) / √12275 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12275)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12275 (gMinus 12275) (gPlus 12275)
      (finiteEnergy 12275 12275 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12275) (hτ : 0 < (paperDesignP 12275).tau0 c) :
    eR c = (2 / (mA 12275 : ℝ)) *
      normSq (BstLean.Part150.bT 12275 12275 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12275).tau0 c)) /
      (2 / (12275 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12275).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12275).tau0 c))⁻¹ •
      BstLean.Part150.bT 12275 12275 (A1 c) (A2 c) c.1.2 ((paperDesignP 12275).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12275 : ℝ)) * normSq (bR c) / (2 / (12275 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12275}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12275) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12275).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12275 : ℝ) * (paperDesignP 12275).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12275 12275 c.1.2 ((paperDesignP 12275).tau0 c) :=
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

end BstLean.Part262.Row12275

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12276
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12276 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12276).real (BstLean.Part211.CentreSource 12276 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12276) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12276 160 (6 / 1000)
  have hj := jS_160_le (n := 12276) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12276 160 (6 / 1000) ^ 2 * 12276 /
      (((12276 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12276 160 (6 / 1000) ^ 2 * 12276 /
      (((12276 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12276 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12276 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12276) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12276 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12276

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12276
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12276) :=
  Ethm (paperCentres 12276) ∩ Ethp (paperCentres 12276)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12276)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12276)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12276) (paperCentres 12276)
  have he : exp (-(45 / 10000 * (12276 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12276 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12276) :=
  (passEvent ∩ agentEv (paperDesignP 12276) (DirectionError 12276) ∩
    agentEv (paperDesignP 12276) (CentreSources 12276 12276)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12276)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12276) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12276) hτ
  have hC := centreSources_ret_charge_row 12276 (paperDesignP 12276) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12276)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12276) (CentreSources 12276 12276)
  direction : analyticBase ⊆ agentEv (paperDesignP 12276) (DirectionError 12276)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12276)) : Set (Ret 12276) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12276)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12276)}
    (hT : (retDist (paperCentres 12276)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12276)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12276)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12276)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12276)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12276)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12276

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12276
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12276 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12276 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12276 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12276 12276 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12276)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12276)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12276
  have hb0 := BstLean.Part150.betaJ_nonneg 12276
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12276 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12276 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12276 * BstLean.Part150.betaJ 12276) * 12276) ≤
      (157551299 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12276)) * 12276 := by gcongr <;> linarith
      _ ≤ ((157551299 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12276 * 12276 *
      (1 + BstLean.Part154.deltaChi 12276 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180336543 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12276 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180336543 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12276 : ℝ) / BstLean.Part154.csC) ≤ (97355019 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12276 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97355019 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12276 : ℝ) * (157551299 / 1000000) +
        2 * (1792 / 10000 / 12276) * (180336543 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97355019 / 1000000) *
          (81 / 1000 / 12276 + (1792 / 10000 / 12276) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12276

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12276
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12276 ∧
    1 ≤ gPlus 12276 ∧ gPlus 12276 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12276 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12276 : ℝ) < √(1 - 2 / (12276 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12276 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12276 (gMinus 12276) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12276 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12276 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12276 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12276)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12276 (gMinus 12276) (gPlus 12276)
      (finiteEnergy 12276 12276 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12276 (gMinus 12276) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12276 (gMinus 12276) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12276 (gMinus 12276) (54 / 100))
    (by linarith : energyRatio 12276 (gMinus 12276) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12276 (gMinus 12276) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12276 * kappa (energyRatio 12276 (gMinus 12276) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12276) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12276 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12276 12276 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12276 12276 (11 / 1000) / √12276 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12276)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12276 * kappa (energyRatio 12276 (gMinus 12276) (54 / 100))) +
      2 * √(12 * gPlus 12276) / 12276 + finiteEnergy 12276 12276 (11 / 1000) / √12276 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12276 θ ∧ meanLowerRoot 12276 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12276 - 2 / (12276 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12276 - 2 / (12276 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12276 θ ^ 2 / gPlus 12276) - 2 / (12276 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12276 * (kappa (meanLowerRoot 12276 θ ^ 2 / gPlus 12276) -
        2 / (12276 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12276) / 12276 -
        finiteEnergy 12276 12276 (11 / 1000) / √12276 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12276 θ ^ 2 / gPlus 12276 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12276)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12276 θ ^ 2 / gPlus 12276 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12276)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12276 θ ^ 2 / gPlus 12276 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12276 ^ 2 ≤
      kappa (meanLowerRoot 12276 θ ^ 2 / gPlus 12276) - 2 / (12276 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12276 *
      (kappa (meanLowerRoot 12276 θ ^ 2 / gPlus 12276) - 2 / (12276 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12276 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12276)
    linarith
  have ht : √(12 * gPlus 12276) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12276 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12276 12276 (11 / 1000) / √12276 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12276)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12276 (gMinus 12276) (gPlus 12276)
      (finiteEnergy 12276 12276 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12276) (hτ : 0 < (paperDesignP 12276).tau0 c) :
    eR c = (2 / (mA 12276 : ℝ)) *
      normSq (BstLean.Part150.bT 12276 12276 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12276).tau0 c)) /
      (2 / (12276 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12276).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12276).tau0 c))⁻¹ •
      BstLean.Part150.bT 12276 12276 (A1 c) (A2 c) c.1.2 ((paperDesignP 12276).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12276 : ℝ)) * normSq (bR c) / (2 / (12276 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12276}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12276) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12276).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12276 : ℝ) * (paperDesignP 12276).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12276 12276 c.1.2 ((paperDesignP 12276).tau0 c) :=
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

end BstLean.Part262.Row12276

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12277
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12277 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12277).real (BstLean.Part211.CentreSource 12277 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12277) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12277 160 (6 / 1000)
  have hj := jS_160_le (n := 12277) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12277 160 (6 / 1000) ^ 2 * 12277 /
      (((12277 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12277 160 (6 / 1000) ^ 2 * 12277 /
      (((12277 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12277 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12277 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12277) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12277 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12277

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12277
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12277) :=
  Ethm (paperCentres 12277) ∩ Ethp (paperCentres 12277)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12277)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12277)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12277) (paperCentres 12277)
  have he : exp (-(45 / 10000 * (12277 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12277 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12277) :=
  (passEvent ∩ agentEv (paperDesignP 12277) (DirectionError 12277) ∩
    agentEv (paperDesignP 12277) (CentreSources 12277 12277)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12277)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12277) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12277) hτ
  have hC := centreSources_ret_charge_row 12277 (paperDesignP 12277) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12277)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12277) (CentreSources 12277 12277)
  direction : analyticBase ⊆ agentEv (paperDesignP 12277) (DirectionError 12277)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12277)) : Set (Ret 12277) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12277)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12277)}
    (hT : (retDist (paperCentres 12277)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12277)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12277)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12277)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12277)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12277)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12277

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12277
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12277 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12277 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12277 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12277 12277 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12277)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12277)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12277
  have hb0 := BstLean.Part150.betaJ_nonneg 12277
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12277 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12277 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12277 * BstLean.Part150.betaJ 12277) * 12277) ≤
      (31511543 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12277)) * 12277 := by gcongr <;> linarith
      _ ≤ ((31511543 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12277 * 12277 *
      (1 + BstLean.Part154.deltaChi 12277 12 + 2 / π) / BstLean.Part154.csC) ≤
      (11271493 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12277 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((11271493 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12277 : ℝ) / BstLean.Part154.csC) ≤ (19471797 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12277 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19471797 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12277 : ℝ) * (31511543 / 200000) +
        2 * (1792 / 10000 / 12277) * (11271493 / 62500) +
        4 * (1 / 2.506628) * 1.036505 * (19471797 / 200000) *
          (81 / 1000 / 12277 + (1792 / 10000 / 12277) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12277

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12277
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12277 ∧
    1 ≤ gPlus 12277 ∧ gPlus 12277 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12277 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12277 : ℝ) < √(1 - 2 / (12277 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12277 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12277 (gMinus 12277) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12277 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12277 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12277 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12277)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12277 (gMinus 12277) (gPlus 12277)
      (finiteEnergy 12277 12277 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12277 (gMinus 12277) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12277 (gMinus 12277) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12277 (gMinus 12277) (54 / 100))
    (by linarith : energyRatio 12277 (gMinus 12277) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12277 (gMinus 12277) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12277 * kappa (energyRatio 12277 (gMinus 12277) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12277) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12277 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12277 12277 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12277 12277 (11 / 1000) / √12277 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12277)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12277 * kappa (energyRatio 12277 (gMinus 12277) (54 / 100))) +
      2 * √(12 * gPlus 12277) / 12277 + finiteEnergy 12277 12277 (11 / 1000) / √12277 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12277 θ ∧ meanLowerRoot 12277 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12277 - 2 / (12277 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12277 - 2 / (12277 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12277 θ ^ 2 / gPlus 12277) - 2 / (12277 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12277 * (kappa (meanLowerRoot 12277 θ ^ 2 / gPlus 12277) -
        2 / (12277 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12277) / 12277 -
        finiteEnergy 12277 12277 (11 / 1000) / √12277 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12277 θ ^ 2 / gPlus 12277 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12277)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12277 θ ^ 2 / gPlus 12277 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12277)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12277 θ ^ 2 / gPlus 12277 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12277 ^ 2 ≤
      kappa (meanLowerRoot 12277 θ ^ 2 / gPlus 12277) - 2 / (12277 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12277 *
      (kappa (meanLowerRoot 12277 θ ^ 2 / gPlus 12277) - 2 / (12277 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12277 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12277)
    linarith
  have ht : √(12 * gPlus 12277) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12277 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12277 12277 (11 / 1000) / √12277 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12277)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12277 (gMinus 12277) (gPlus 12277)
      (finiteEnergy 12277 12277 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12277) (hτ : 0 < (paperDesignP 12277).tau0 c) :
    eR c = (2 / (mA 12277 : ℝ)) *
      normSq (BstLean.Part150.bT 12277 12277 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12277).tau0 c)) /
      (2 / (12277 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12277).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12277).tau0 c))⁻¹ •
      BstLean.Part150.bT 12277 12277 (A1 c) (A2 c) c.1.2 ((paperDesignP 12277).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12277 : ℝ)) * normSq (bR c) / (2 / (12277 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12277}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12277) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12277).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12277 : ℝ) * (paperDesignP 12277).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12277 12277 c.1.2 ((paperDesignP 12277).tau0 c) :=
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

end BstLean.Part262.Row12277

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12278
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12278 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12278).real (BstLean.Part211.CentreSource 12278 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12278) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12278 160 (6 / 1000)
  have hj := jS_160_le (n := 12278) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12278 160 (6 / 1000) ^ 2 * 12278 /
      (((12278 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12278 160 (6 / 1000) ^ 2 * 12278 /
      (((12278 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12278 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12278 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12278) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12278 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12278

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12278
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12278) :=
  Ethm (paperCentres 12278) ∩ Ethp (paperCentres 12278)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12278)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12278)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12278) (paperCentres 12278)
  have he : exp (-(45 / 10000 * (12278 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12278 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12278) :=
  (passEvent ∩ agentEv (paperDesignP 12278) (DirectionError 12278) ∩
    agentEv (paperDesignP 12278) (CentreSources 12278 12278)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12278)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12278) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12278) hτ
  have hC := centreSources_ret_charge_row 12278 (paperDesignP 12278) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12278)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12278) (CentreSources 12278 12278)
  direction : analyticBase ⊆ agentEv (paperDesignP 12278) (DirectionError 12278)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12278)) : Set (Ret 12278) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12278)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12278)}
    (hT : (retDist (paperCentres 12278)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12278)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12278)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12278)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12278)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12278)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12278

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12278
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12278 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12278 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12278 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12278 12278 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12278)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12278)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12278
  have hb0 := BstLean.Part150.betaJ_nonneg 12278
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12278 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12278 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12278 * BstLean.Part150.betaJ 12278) * 12278) ≤
      (39391033 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12278)) * 12278 := by gcongr <;> linarith
      _ ≤ ((39391033 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12278 * 12278 *
      (1 + BstLean.Part154.deltaChi 12278 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180351233 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12278 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180351233 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12278 : ℝ) / BstLean.Part154.csC) ≤ (1947259 / 20000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12278 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((1947259 / 20000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12278 : ℝ) * (39391033 / 250000) +
        2 * (1792 / 10000 / 12278) * (180351233 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (1947259 / 20000) *
          (81 / 1000 / 12278 + (1792 / 10000 / 12278) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12278

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12278
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12278 ∧
    1 ≤ gPlus 12278 ∧ gPlus 12278 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12278 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12278 : ℝ) < √(1 - 2 / (12278 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12278 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12278 (gMinus 12278) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12278 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12278 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12278 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12278)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12278 (gMinus 12278) (gPlus 12278)
      (finiteEnergy 12278 12278 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12278 (gMinus 12278) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12278 (gMinus 12278) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12278 (gMinus 12278) (54 / 100))
    (by linarith : energyRatio 12278 (gMinus 12278) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12278 (gMinus 12278) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12278 * kappa (energyRatio 12278 (gMinus 12278) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12278) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12278 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12278 12278 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12278 12278 (11 / 1000) / √12278 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12278)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12278 * kappa (energyRatio 12278 (gMinus 12278) (54 / 100))) +
      2 * √(12 * gPlus 12278) / 12278 + finiteEnergy 12278 12278 (11 / 1000) / √12278 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12278 θ ∧ meanLowerRoot 12278 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12278 - 2 / (12278 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12278 - 2 / (12278 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12278 θ ^ 2 / gPlus 12278) - 2 / (12278 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12278 * (kappa (meanLowerRoot 12278 θ ^ 2 / gPlus 12278) -
        2 / (12278 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12278) / 12278 -
        finiteEnergy 12278 12278 (11 / 1000) / √12278 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12278 θ ^ 2 / gPlus 12278 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12278)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12278 θ ^ 2 / gPlus 12278 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12278)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12278 θ ^ 2 / gPlus 12278 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12278 ^ 2 ≤
      kappa (meanLowerRoot 12278 θ ^ 2 / gPlus 12278) - 2 / (12278 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12278 *
      (kappa (meanLowerRoot 12278 θ ^ 2 / gPlus 12278) - 2 / (12278 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12278 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12278)
    linarith
  have ht : √(12 * gPlus 12278) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12278 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12278 12278 (11 / 1000) / √12278 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12278)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12278 (gMinus 12278) (gPlus 12278)
      (finiteEnergy 12278 12278 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12278) (hτ : 0 < (paperDesignP 12278).tau0 c) :
    eR c = (2 / (mA 12278 : ℝ)) *
      normSq (BstLean.Part150.bT 12278 12278 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12278).tau0 c)) /
      (2 / (12278 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12278).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12278).tau0 c))⁻¹ •
      BstLean.Part150.bT 12278 12278 (A1 c) (A2 c) c.1.2 ((paperDesignP 12278).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12278 : ℝ)) * normSq (bR c) / (2 / (12278 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12278}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12278) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12278).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12278 : ℝ) * (paperDesignP 12278).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12278 12278 c.1.2 ((paperDesignP 12278).tau0 c) :=
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

end BstLean.Part262.Row12278

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12279
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12279 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12279).real (BstLean.Part211.CentreSource 12279 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12279) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12279 160 (6 / 1000)
  have hj := jS_160_le (n := 12279) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12279 160 (6 / 1000) ^ 2 * 12279 /
      (((12279 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12279 160 (6 / 1000) ^ 2 * 12279 /
      (((12279 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12279 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12279 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12279) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12279 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12279

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12279
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12279) :=
  Ethm (paperCentres 12279) ∩ Ethp (paperCentres 12279)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12279)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12279)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12279) (paperCentres 12279)
  have he : exp (-(45 / 10000 * (12279 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12279 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12279) :=
  (passEvent ∩ agentEv (paperDesignP 12279) (DirectionError 12279) ∩
    agentEv (paperDesignP 12279) (CentreSources 12279 12279)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12279)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12279) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12279) hτ
  have hC := centreSources_ret_charge_row 12279 (paperDesignP 12279) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12279)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12279) (CentreSources 12279 12279)
  direction : analyticBase ⊆ agentEv (paperDesignP 12279) (DirectionError 12279)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12279)) : Set (Ret 12279) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12279)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12279)}
    (hT : (retDist (paperCentres 12279)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12279)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12279)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12279)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12279)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12279)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12279

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12279
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12279 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12279 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12279 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12279 12279 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12279)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12279)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12279
  have hb0 := BstLean.Part150.betaJ_nonneg 12279
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12279 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12279 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12279 * BstLean.Part150.betaJ 12279) * 12279) ≤
      (39392637 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12279)) * 12279 := by gcongr <;> linarith
      _ ≤ ((39392637 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12279 * 12279 *
      (1 + BstLean.Part154.deltaChi 12279 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180358577 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12279 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180358577 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12279 : ℝ) / BstLean.Part154.csC) ≤ (48683457 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12279 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48683457 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12279 : ℝ) * (39392637 / 250000) +
        2 * (1792 / 10000 / 12279) * (180358577 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (48683457 / 500000) *
          (81 / 1000 / 12279 + (1792 / 10000 / 12279) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12279

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12279
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12279 ∧
    1 ≤ gPlus 12279 ∧ gPlus 12279 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12279 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12279 : ℝ) < √(1 - 2 / (12279 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12279 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12279 (gMinus 12279) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12279 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12279 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12279 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12279)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12279 (gMinus 12279) (gPlus 12279)
      (finiteEnergy 12279 12279 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12279 (gMinus 12279) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12279 (gMinus 12279) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12279 (gMinus 12279) (54 / 100))
    (by linarith : energyRatio 12279 (gMinus 12279) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12279 (gMinus 12279) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12279 * kappa (energyRatio 12279 (gMinus 12279) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12279) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12279 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12279 12279 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12279 12279 (11 / 1000) / √12279 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12279)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12279 * kappa (energyRatio 12279 (gMinus 12279) (54 / 100))) +
      2 * √(12 * gPlus 12279) / 12279 + finiteEnergy 12279 12279 (11 / 1000) / √12279 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12279 θ ∧ meanLowerRoot 12279 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12279 - 2 / (12279 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12279 - 2 / (12279 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12279 θ ^ 2 / gPlus 12279) - 2 / (12279 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12279 * (kappa (meanLowerRoot 12279 θ ^ 2 / gPlus 12279) -
        2 / (12279 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12279) / 12279 -
        finiteEnergy 12279 12279 (11 / 1000) / √12279 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12279 θ ^ 2 / gPlus 12279 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12279)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12279 θ ^ 2 / gPlus 12279 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12279)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12279 θ ^ 2 / gPlus 12279 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12279 ^ 2 ≤
      kappa (meanLowerRoot 12279 θ ^ 2 / gPlus 12279) - 2 / (12279 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12279 *
      (kappa (meanLowerRoot 12279 θ ^ 2 / gPlus 12279) - 2 / (12279 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12279 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12279)
    linarith
  have ht : √(12 * gPlus 12279) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12279 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12279 12279 (11 / 1000) / √12279 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12279)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12279 (gMinus 12279) (gPlus 12279)
      (finiteEnergy 12279 12279 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12279) (hτ : 0 < (paperDesignP 12279).tau0 c) :
    eR c = (2 / (mA 12279 : ℝ)) *
      normSq (BstLean.Part150.bT 12279 12279 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12279).tau0 c)) /
      (2 / (12279 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12279).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12279).tau0 c))⁻¹ •
      BstLean.Part150.bT 12279 12279 (A1 c) (A2 c) c.1.2 ((paperDesignP 12279).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12279 : ℝ)) * normSq (bR c) / (2 / (12279 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12279}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12279) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12279).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12279 : ℝ) * (paperDesignP 12279).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12279 12279 c.1.2 ((paperDesignP 12279).tau0 c) :=
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

end BstLean.Part262.Row12279

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12280
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12280 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12280).real (BstLean.Part211.CentreSource 12280 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12280) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12280 160 (6 / 1000)
  have hj := jS_160_le (n := 12280) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12280 160 (6 / 1000) ^ 2 * 12280 /
      (((12280 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12280 160 (6 / 1000) ^ 2 * 12280 /
      (((12280 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12280 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12280 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12280) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12280 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12280

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12280
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12280) :=
  Ethm (paperCentres 12280) ∩ Ethp (paperCentres 12280)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12280)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12280)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12280) (paperCentres 12280)
  have he : exp (-(45 / 10000 * (12280 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12280 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12280) :=
  (passEvent ∩ agentEv (paperDesignP 12280) (DirectionError 12280) ∩
    agentEv (paperDesignP 12280) (CentreSources 12280 12280)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12280)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12280) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12280) hτ
  have hC := centreSources_ret_charge_row 12280 (paperDesignP 12280) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12280)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12280) (CentreSources 12280 12280)
  direction : analyticBase ⊆ agentEv (paperDesignP 12280) (DirectionError 12280)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12280)) : Set (Ret 12280) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12280)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12280)}
    (hT : (retDist (paperCentres 12280)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12280)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12280)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12280)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12280)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12280)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12280

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12280
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12280 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12280 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12280 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12280 12280 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12280)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12280)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12280
  have hb0 := BstLean.Part150.betaJ_nonneg 12280
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12280 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12280 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12280 * BstLean.Part150.betaJ 12280) * 12280) ≤
      (39394241 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12280)) * 12280 := by gcongr <;> linarith
      _ ≤ ((39394241 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12280 * 12280 *
      (1 + BstLean.Part154.deltaChi 12280 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180365921 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12280 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180365921 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12280 : ℝ) / BstLean.Part154.csC) ≤ (97370879 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12280 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97370879 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12280 : ℝ) * (39394241 / 250000) +
        2 * (1792 / 10000 / 12280) * (180365921 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97370879 / 1000000) *
          (81 / 1000 / 12280 + (1792 / 10000 / 12280) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12280

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12280
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12280 ∧
    1 ≤ gPlus 12280 ∧ gPlus 12280 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12280 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12280 : ℝ) < √(1 - 2 / (12280 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12280 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12280 (gMinus 12280) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12280 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12280 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12280 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12280)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12280 (gMinus 12280) (gPlus 12280)
      (finiteEnergy 12280 12280 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12280 (gMinus 12280) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12280 (gMinus 12280) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12280 (gMinus 12280) (54 / 100))
    (by linarith : energyRatio 12280 (gMinus 12280) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12280 (gMinus 12280) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12280 * kappa (energyRatio 12280 (gMinus 12280) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12280) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12280 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12280 12280 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12280 12280 (11 / 1000) / √12280 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12280)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12280 * kappa (energyRatio 12280 (gMinus 12280) (54 / 100))) +
      2 * √(12 * gPlus 12280) / 12280 + finiteEnergy 12280 12280 (11 / 1000) / √12280 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12280 θ ∧ meanLowerRoot 12280 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12280 - 2 / (12280 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12280 - 2 / (12280 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12280 θ ^ 2 / gPlus 12280) - 2 / (12280 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12280 * (kappa (meanLowerRoot 12280 θ ^ 2 / gPlus 12280) -
        2 / (12280 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12280) / 12280 -
        finiteEnergy 12280 12280 (11 / 1000) / √12280 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12280 θ ^ 2 / gPlus 12280 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12280)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12280 θ ^ 2 / gPlus 12280 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12280)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12280 θ ^ 2 / gPlus 12280 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12280 ^ 2 ≤
      kappa (meanLowerRoot 12280 θ ^ 2 / gPlus 12280) - 2 / (12280 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12280 *
      (kappa (meanLowerRoot 12280 θ ^ 2 / gPlus 12280) - 2 / (12280 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12280 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12280)
    linarith
  have ht : √(12 * gPlus 12280) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12280 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12280 12280 (11 / 1000) / √12280 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12280)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12280 (gMinus 12280) (gPlus 12280)
      (finiteEnergy 12280 12280 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12280) (hτ : 0 < (paperDesignP 12280).tau0 c) :
    eR c = (2 / (mA 12280 : ℝ)) *
      normSq (BstLean.Part150.bT 12280 12280 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12280).tau0 c)) /
      (2 / (12280 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12280).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12280).tau0 c))⁻¹ •
      BstLean.Part150.bT 12280 12280 (A1 c) (A2 c) c.1.2 ((paperDesignP 12280).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12280 : ℝ)) * normSq (bR c) / (2 / (12280 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12280}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12280) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12280).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12280 : ℝ) * (paperDesignP 12280).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12280 12280 c.1.2 ((paperDesignP 12280).tau0 c) :=
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

end BstLean.Part262.Row12280

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12281
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12281 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12281).real (BstLean.Part211.CentreSource 12281 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12281) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12281 160 (6 / 1000)
  have hj := jS_160_le (n := 12281) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12281 160 (6 / 1000) ^ 2 * 12281 /
      (((12281 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12281 160 (6 / 1000) ^ 2 * 12281 /
      (((12281 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12281 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12281 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12281) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12281 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12281

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12281
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12281) :=
  Ethm (paperCentres 12281) ∩ Ethp (paperCentres 12281)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12281)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12281)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12281) (paperCentres 12281)
  have he : exp (-(45 / 10000 * (12281 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12281 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12281) :=
  (passEvent ∩ agentEv (paperDesignP 12281) (DirectionError 12281) ∩
    agentEv (paperDesignP 12281) (CentreSources 12281 12281)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12281)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12281) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12281) hτ
  have hC := centreSources_ret_charge_row 12281 (paperDesignP 12281) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12281)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12281) (CentreSources 12281 12281)
  direction : analyticBase ⊆ agentEv (paperDesignP 12281) (DirectionError 12281)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12281)) : Set (Ret 12281) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12281)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12281)}
    (hT : (retDist (paperCentres 12281)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12281)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12281)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12281)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12281)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12281)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12281

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12281
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12281 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12281 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12281 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12281 12281 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12281)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12281)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12281
  have hb0 := BstLean.Part150.betaJ_nonneg 12281
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12281 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12281 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12281 * BstLean.Part150.betaJ 12281) * 12281) ≤
      (7879169 / 50000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12281)) * 12281 := by gcongr <;> linarith
      _ ≤ ((7879169 / 50000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12281 * 12281 *
      (1 + BstLean.Part154.deltaChi 12281 12 + 2 / π) / BstLean.Part154.csC) ≤
      (36074653 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12281 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((36074653 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12281 : ℝ) / BstLean.Part154.csC) ≤ (24343711 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12281 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((24343711 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12281 : ℝ) * (7879169 / 50000) +
        2 * (1792 / 10000 / 12281) * (36074653 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (24343711 / 250000) *
          (81 / 1000 / 12281 + (1792 / 10000 / 12281) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12281

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12281
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12281 ∧
    1 ≤ gPlus 12281 ∧ gPlus 12281 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12281 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12281 : ℝ) < √(1 - 2 / (12281 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12281 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12281 (gMinus 12281) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12281 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12281 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12281 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12281)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12281 (gMinus 12281) (gPlus 12281)
      (finiteEnergy 12281 12281 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12281 (gMinus 12281) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12281 (gMinus 12281) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12281 (gMinus 12281) (54 / 100))
    (by linarith : energyRatio 12281 (gMinus 12281) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12281 (gMinus 12281) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12281 * kappa (energyRatio 12281 (gMinus 12281) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12281) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12281 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12281 12281 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12281 12281 (11 / 1000) / √12281 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12281)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12281 * kappa (energyRatio 12281 (gMinus 12281) (54 / 100))) +
      2 * √(12 * gPlus 12281) / 12281 + finiteEnergy 12281 12281 (11 / 1000) / √12281 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12281 θ ∧ meanLowerRoot 12281 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12281 - 2 / (12281 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12281 - 2 / (12281 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12281 θ ^ 2 / gPlus 12281) - 2 / (12281 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12281 * (kappa (meanLowerRoot 12281 θ ^ 2 / gPlus 12281) -
        2 / (12281 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12281) / 12281 -
        finiteEnergy 12281 12281 (11 / 1000) / √12281 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12281 θ ^ 2 / gPlus 12281 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12281)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12281 θ ^ 2 / gPlus 12281 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12281)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12281 θ ^ 2 / gPlus 12281 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12281 ^ 2 ≤
      kappa (meanLowerRoot 12281 θ ^ 2 / gPlus 12281) - 2 / (12281 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12281 *
      (kappa (meanLowerRoot 12281 θ ^ 2 / gPlus 12281) - 2 / (12281 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12281 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12281)
    linarith
  have ht : √(12 * gPlus 12281) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12281 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12281 12281 (11 / 1000) / √12281 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12281)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12281 (gMinus 12281) (gPlus 12281)
      (finiteEnergy 12281 12281 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12281) (hτ : 0 < (paperDesignP 12281).tau0 c) :
    eR c = (2 / (mA 12281 : ℝ)) *
      normSq (BstLean.Part150.bT 12281 12281 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12281).tau0 c)) /
      (2 / (12281 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12281).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12281).tau0 c))⁻¹ •
      BstLean.Part150.bT 12281 12281 (A1 c) (A2 c) c.1.2 ((paperDesignP 12281).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12281 : ℝ)) * normSq (bR c) / (2 / (12281 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12281}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12281) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12281).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12281 : ℝ) * (paperDesignP 12281).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12281 12281 c.1.2 ((paperDesignP 12281).tau0 c) :=
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

end BstLean.Part262.Row12281

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12282
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12282 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12282).real (BstLean.Part211.CentreSource 12282 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12282) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12282 160 (6 / 1000)
  have hj := jS_160_le (n := 12282) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12282 160 (6 / 1000) ^ 2 * 12282 /
      (((12282 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12282 160 (6 / 1000) ^ 2 * 12282 /
      (((12282 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12282 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12282 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12282) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12282 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12282

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12282
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12282) :=
  Ethm (paperCentres 12282) ∩ Ethp (paperCentres 12282)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12282)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12282)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12282) (paperCentres 12282)
  have he : exp (-(45 / 10000 * (12282 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12282 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12282) :=
  (passEvent ∩ agentEv (paperDesignP 12282) (DirectionError 12282) ∩
    agentEv (paperDesignP 12282) (CentreSources 12282 12282)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12282)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12282) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12282) hτ
  have hC := centreSources_ret_charge_row 12282 (paperDesignP 12282) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12282)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12282) (CentreSources 12282 12282)
  direction : analyticBase ⊆ agentEv (paperDesignP 12282) (DirectionError 12282)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12282)) : Set (Ret 12282) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12282)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12282)}
    (hT : (retDist (paperCentres 12282)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12282)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12282)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12282)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12282)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12282)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12282

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12282
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12282 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12282 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12282 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12282 12282 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12282)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12282)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12282
  have hb0 := BstLean.Part150.betaJ_nonneg 12282
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12282 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12282 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12282 * BstLean.Part150.betaJ 12282) * 12282) ≤
      (39397449 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12282)) * 12282 := by gcongr <;> linarith
      _ ≤ ((39397449 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12282 * 12282 *
      (1 + BstLean.Part154.deltaChi 12282 12 + 2 / π) / BstLean.Part154.csC) ≤
      (2818447 / 15625) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12282 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((2818447 / 15625) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12282 : ℝ) / BstLean.Part154.csC) ≤ (12172351 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12282 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12172351 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12282 : ℝ) * (39397449 / 250000) +
        2 * (1792 / 10000 / 12282) * (2818447 / 15625) +
        4 * (1 / 2.506628) * 1.036505 * (12172351 / 125000) *
          (81 / 1000 / 12282 + (1792 / 10000 / 12282) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12282

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12282
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12282 ∧
    1 ≤ gPlus 12282 ∧ gPlus 12282 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12282 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12282 : ℝ) < √(1 - 2 / (12282 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12282 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12282 (gMinus 12282) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12282 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12282 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12282 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12282)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12282 (gMinus 12282) (gPlus 12282)
      (finiteEnergy 12282 12282 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12282 (gMinus 12282) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12282 (gMinus 12282) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12282 (gMinus 12282) (54 / 100))
    (by linarith : energyRatio 12282 (gMinus 12282) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12282 (gMinus 12282) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12282 * kappa (energyRatio 12282 (gMinus 12282) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12282) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12282 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12282 12282 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12282 12282 (11 / 1000) / √12282 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12282)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12282 * kappa (energyRatio 12282 (gMinus 12282) (54 / 100))) +
      2 * √(12 * gPlus 12282) / 12282 + finiteEnergy 12282 12282 (11 / 1000) / √12282 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12282 θ ∧ meanLowerRoot 12282 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12282 - 2 / (12282 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12282 - 2 / (12282 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12282 θ ^ 2 / gPlus 12282) - 2 / (12282 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12282 * (kappa (meanLowerRoot 12282 θ ^ 2 / gPlus 12282) -
        2 / (12282 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12282) / 12282 -
        finiteEnergy 12282 12282 (11 / 1000) / √12282 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12282 θ ^ 2 / gPlus 12282 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12282)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12282 θ ^ 2 / gPlus 12282 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12282)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12282 θ ^ 2 / gPlus 12282 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12282 ^ 2 ≤
      kappa (meanLowerRoot 12282 θ ^ 2 / gPlus 12282) - 2 / (12282 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12282 *
      (kappa (meanLowerRoot 12282 θ ^ 2 / gPlus 12282) - 2 / (12282 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12282 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12282)
    linarith
  have ht : √(12 * gPlus 12282) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12282 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12282 12282 (11 / 1000) / √12282 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12282)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12282 (gMinus 12282) (gPlus 12282)
      (finiteEnergy 12282 12282 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12282) (hτ : 0 < (paperDesignP 12282).tau0 c) :
    eR c = (2 / (mA 12282 : ℝ)) *
      normSq (BstLean.Part150.bT 12282 12282 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12282).tau0 c)) /
      (2 / (12282 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12282).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12282).tau0 c))⁻¹ •
      BstLean.Part150.bT 12282 12282 (A1 c) (A2 c) c.1.2 ((paperDesignP 12282).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12282 : ℝ)) * normSq (bR c) / (2 / (12282 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12282}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12282) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12282).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12282 : ℝ) * (paperDesignP 12282).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12282 12282 c.1.2 ((paperDesignP 12282).tau0 c) :=
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

end BstLean.Part262.Row12282

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12283
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12283 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12283).real (BstLean.Part211.CentreSource 12283 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12283) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12283 160 (6 / 1000)
  have hj := jS_160_le (n := 12283) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12283 160 (6 / 1000) ^ 2 * 12283 /
      (((12283 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12283 160 (6 / 1000) ^ 2 * 12283 /
      (((12283 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12283 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12283 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12283) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12283 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12283

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12283
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12283) :=
  Ethm (paperCentres 12283) ∩ Ethp (paperCentres 12283)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12283)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12283)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12283) (paperCentres 12283)
  have he : exp (-(45 / 10000 * (12283 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12283 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12283) :=
  (passEvent ∩ agentEv (paperDesignP 12283) (DirectionError 12283) ∩
    agentEv (paperDesignP 12283) (CentreSources 12283 12283)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12283)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12283) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12283) hτ
  have hC := centreSources_ret_charge_row 12283 (paperDesignP 12283) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12283)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12283) (CentreSources 12283 12283)
  direction : analyticBase ⊆ agentEv (paperDesignP 12283) (DirectionError 12283)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12283)) : Set (Ret 12283) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12283)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12283)}
    (hT : (retDist (paperCentres 12283)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12283)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12283)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12283)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12283)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12283)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12283

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12283
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12283 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12283 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12283 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12283 12283 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12283)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12283)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12283
  have hb0 := BstLean.Part150.betaJ_nonneg 12283
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12283 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12283 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12283 * BstLean.Part150.betaJ 12283) * 12283) ≤
      (157596211 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12283)) * 12283 := by gcongr <;> linarith
      _ ≤ ((157596211 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12283 * 12283 *
      (1 + BstLean.Part154.deltaChi 12283 12 + 2 / π) / BstLean.Part154.csC) ≤
      (11274247 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12283 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((11274247 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12283 : ℝ) / BstLean.Part154.csC) ≤ (24345693 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12283 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((24345693 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12283 : ℝ) * (157596211 / 1000000) +
        2 * (1792 / 10000 / 12283) * (11274247 / 62500) +
        4 * (1 / 2.506628) * 1.036505 * (24345693 / 250000) *
          (81 / 1000 / 12283 + (1792 / 10000 / 12283) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12283

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12283
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12283 ∧
    1 ≤ gPlus 12283 ∧ gPlus 12283 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12283 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12283 : ℝ) < √(1 - 2 / (12283 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12283 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12283 (gMinus 12283) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12283 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12283 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12283 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12283)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12283 (gMinus 12283) (gPlus 12283)
      (finiteEnergy 12283 12283 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12283 (gMinus 12283) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12283 (gMinus 12283) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12283 (gMinus 12283) (54 / 100))
    (by linarith : energyRatio 12283 (gMinus 12283) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12283 (gMinus 12283) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12283 * kappa (energyRatio 12283 (gMinus 12283) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12283) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12283 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12283 12283 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12283 12283 (11 / 1000) / √12283 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12283)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12283 * kappa (energyRatio 12283 (gMinus 12283) (54 / 100))) +
      2 * √(12 * gPlus 12283) / 12283 + finiteEnergy 12283 12283 (11 / 1000) / √12283 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12283 θ ∧ meanLowerRoot 12283 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12283 - 2 / (12283 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12283 - 2 / (12283 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12283 θ ^ 2 / gPlus 12283) - 2 / (12283 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12283 * (kappa (meanLowerRoot 12283 θ ^ 2 / gPlus 12283) -
        2 / (12283 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12283) / 12283 -
        finiteEnergy 12283 12283 (11 / 1000) / √12283 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12283 θ ^ 2 / gPlus 12283 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12283)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12283 θ ^ 2 / gPlus 12283 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12283)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12283 θ ^ 2 / gPlus 12283 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12283 ^ 2 ≤
      kappa (meanLowerRoot 12283 θ ^ 2 / gPlus 12283) - 2 / (12283 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12283 *
      (kappa (meanLowerRoot 12283 θ ^ 2 / gPlus 12283) - 2 / (12283 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12283 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12283)
    linarith
  have ht : √(12 * gPlus 12283) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12283 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12283 12283 (11 / 1000) / √12283 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12283)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12283 (gMinus 12283) (gPlus 12283)
      (finiteEnergy 12283 12283 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12283) (hτ : 0 < (paperDesignP 12283).tau0 c) :
    eR c = (2 / (mA 12283 : ℝ)) *
      normSq (BstLean.Part150.bT 12283 12283 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12283).tau0 c)) /
      (2 / (12283 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12283).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12283).tau0 c))⁻¹ •
      BstLean.Part150.bT 12283 12283 (A1 c) (A2 c) c.1.2 ((paperDesignP 12283).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12283 : ℝ)) * normSq (bR c) / (2 / (12283 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12283}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12283) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12283).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12283 : ℝ) * (paperDesignP 12283).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12283 12283 c.1.2 ((paperDesignP 12283).tau0 c) :=
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

end BstLean.Part262.Row12283

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12284
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12284 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12284).real (BstLean.Part211.CentreSource 12284 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12284) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12284 160 (6 / 1000)
  have hj := jS_160_le (n := 12284) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12284 160 (6 / 1000) ^ 2 * 12284 /
      (((12284 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12284 160 (6 / 1000) ^ 2 * 12284 /
      (((12284 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12284 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12284 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12284) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12284 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12284

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12284
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12284) :=
  Ethm (paperCentres 12284) ∩ Ethp (paperCentres 12284)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12284)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12284)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12284) (paperCentres 12284)
  have he : exp (-(45 / 10000 * (12284 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12284 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12284) :=
  (passEvent ∩ agentEv (paperDesignP 12284) (DirectionError 12284) ∩
    agentEv (paperDesignP 12284) (CentreSources 12284 12284)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12284)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12284) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12284) hτ
  have hC := centreSources_ret_charge_row 12284 (paperDesignP 12284) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12284)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12284) (CentreSources 12284 12284)
  direction : analyticBase ⊆ agentEv (paperDesignP 12284) (DirectionError 12284)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12284)) : Set (Ret 12284) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12284)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12284)}
    (hT : (retDist (paperCentres 12284)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12284)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12284)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12284)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12284)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12284)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12284

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12284
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12284 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12284 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12284 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12284 12284 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12284)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12284)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12284
  have hb0 := BstLean.Part150.betaJ_nonneg 12284
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12284 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12284 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12284 * BstLean.Part150.betaJ 12284) * 12284) ≤
      (78801313 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12284)) * 12284 := by gcongr <;> linarith
      _ ≤ ((78801313 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12284 * 12284 *
      (1 + BstLean.Part154.deltaChi 12284 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90197647 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12284 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90197647 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12284 : ℝ) / BstLean.Part154.csC) ≤ (6086671 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12284 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((6086671 / 62500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12284 : ℝ) * (78801313 / 500000) +
        2 * (1792 / 10000 / 12284) * (90197647 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (6086671 / 62500) *
          (81 / 1000 / 12284 + (1792 / 10000 / 12284) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12284

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12284
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12284 ∧
    1 ≤ gPlus 12284 ∧ gPlus 12284 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12284 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12284 : ℝ) < √(1 - 2 / (12284 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12284 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12284 (gMinus 12284) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12284 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12284 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12284 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12284)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12284 (gMinus 12284) (gPlus 12284)
      (finiteEnergy 12284 12284 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12284 (gMinus 12284) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12284 (gMinus 12284) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12284 (gMinus 12284) (54 / 100))
    (by linarith : energyRatio 12284 (gMinus 12284) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12284 (gMinus 12284) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12284 * kappa (energyRatio 12284 (gMinus 12284) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12284) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12284 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12284 12284 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12284 12284 (11 / 1000) / √12284 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12284)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12284 * kappa (energyRatio 12284 (gMinus 12284) (54 / 100))) +
      2 * √(12 * gPlus 12284) / 12284 + finiteEnergy 12284 12284 (11 / 1000) / √12284 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12284 θ ∧ meanLowerRoot 12284 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12284 - 2 / (12284 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12284 - 2 / (12284 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12284 θ ^ 2 / gPlus 12284) - 2 / (12284 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12284 * (kappa (meanLowerRoot 12284 θ ^ 2 / gPlus 12284) -
        2 / (12284 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12284) / 12284 -
        finiteEnergy 12284 12284 (11 / 1000) / √12284 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12284 θ ^ 2 / gPlus 12284 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12284)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12284 θ ^ 2 / gPlus 12284 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12284)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12284 θ ^ 2 / gPlus 12284 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12284 ^ 2 ≤
      kappa (meanLowerRoot 12284 θ ^ 2 / gPlus 12284) - 2 / (12284 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12284 *
      (kappa (meanLowerRoot 12284 θ ^ 2 / gPlus 12284) - 2 / (12284 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12284 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12284)
    linarith
  have ht : √(12 * gPlus 12284) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12284 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12284 12284 (11 / 1000) / √12284 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12284)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12284 (gMinus 12284) (gPlus 12284)
      (finiteEnergy 12284 12284 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12284) (hτ : 0 < (paperDesignP 12284).tau0 c) :
    eR c = (2 / (mA 12284 : ℝ)) *
      normSq (BstLean.Part150.bT 12284 12284 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12284).tau0 c)) /
      (2 / (12284 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12284).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12284).tau0 c))⁻¹ •
      BstLean.Part150.bT 12284 12284 (A1 c) (A2 c) c.1.2 ((paperDesignP 12284).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12284 : ℝ)) * normSq (bR c) / (2 / (12284 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12284}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12284) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12284).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12284 : ℝ) * (paperDesignP 12284).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12284 12284 c.1.2 ((paperDesignP 12284).tau0 c) :=
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

end BstLean.Part262.Row12284

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12285
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12285 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12285).real (BstLean.Part211.CentreSource 12285 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12285) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12285 160 (6 / 1000)
  have hj := jS_160_le (n := 12285) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12285 160 (6 / 1000) ^ 2 * 12285 /
      (((12285 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12285 160 (6 / 1000) ^ 2 * 12285 /
      (((12285 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12285 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12285 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12285) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12285 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12285

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12285
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12285) :=
  Ethm (paperCentres 12285) ∩ Ethp (paperCentres 12285)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12285)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12285)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12285) (paperCentres 12285)
  have he : exp (-(45 / 10000 * (12285 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12285 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12285) :=
  (passEvent ∩ agentEv (paperDesignP 12285) (DirectionError 12285) ∩
    agentEv (paperDesignP 12285) (CentreSources 12285 12285)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12285)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12285) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12285) hτ
  have hC := centreSources_ret_charge_row 12285 (paperDesignP 12285) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12285)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12285) (CentreSources 12285 12285)
  direction : analyticBase ⊆ agentEv (paperDesignP 12285) (DirectionError 12285)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12285)) : Set (Ret 12285) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12285)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12285)}
    (hT : (retDist (paperCentres 12285)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12285)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12285)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12285)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12285)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12285)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12285

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12285
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12285 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12285 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12285 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12285 12285 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12285)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12285)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12285
  have hb0 := BstLean.Part150.betaJ_nonneg 12285
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12285 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12285 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12285 * BstLean.Part150.betaJ 12285) * 12285) ≤
      (157609041 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12285)) * 12285 := by gcongr <;> linarith
      _ ≤ ((157609041 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12285 * 12285 *
      (1 + BstLean.Part154.deltaChi 12285 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180402637 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12285 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180402637 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12285 : ℝ) / BstLean.Part154.csC) ≤ (973907 / 10000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12285 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((973907 / 10000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12285 : ℝ) * (157609041 / 1000000) +
        2 * (1792 / 10000 / 12285) * (180402637 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (973907 / 10000) *
          (81 / 1000 / 12285 + (1792 / 10000 / 12285) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12285

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12285
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12285 ∧
    1 ≤ gPlus 12285 ∧ gPlus 12285 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12285 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12285 : ℝ) < √(1 - 2 / (12285 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12285 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12285 (gMinus 12285) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12285 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12285 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12285 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12285)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12285 (gMinus 12285) (gPlus 12285)
      (finiteEnergy 12285 12285 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12285 (gMinus 12285) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12285 (gMinus 12285) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12285 (gMinus 12285) (54 / 100))
    (by linarith : energyRatio 12285 (gMinus 12285) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12285 (gMinus 12285) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12285 * kappa (energyRatio 12285 (gMinus 12285) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12285) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12285 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12285 12285 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12285 12285 (11 / 1000) / √12285 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12285)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12285 * kappa (energyRatio 12285 (gMinus 12285) (54 / 100))) +
      2 * √(12 * gPlus 12285) / 12285 + finiteEnergy 12285 12285 (11 / 1000) / √12285 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12285 θ ∧ meanLowerRoot 12285 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12285 - 2 / (12285 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12285 - 2 / (12285 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12285 θ ^ 2 / gPlus 12285) - 2 / (12285 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12285 * (kappa (meanLowerRoot 12285 θ ^ 2 / gPlus 12285) -
        2 / (12285 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12285) / 12285 -
        finiteEnergy 12285 12285 (11 / 1000) / √12285 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12285 θ ^ 2 / gPlus 12285 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12285)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12285 θ ^ 2 / gPlus 12285 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12285)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12285 θ ^ 2 / gPlus 12285 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12285 ^ 2 ≤
      kappa (meanLowerRoot 12285 θ ^ 2 / gPlus 12285) - 2 / (12285 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12285 *
      (kappa (meanLowerRoot 12285 θ ^ 2 / gPlus 12285) - 2 / (12285 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12285 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12285)
    linarith
  have ht : √(12 * gPlus 12285) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12285 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12285 12285 (11 / 1000) / √12285 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12285)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12285 (gMinus 12285) (gPlus 12285)
      (finiteEnergy 12285 12285 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12285) (hτ : 0 < (paperDesignP 12285).tau0 c) :
    eR c = (2 / (mA 12285 : ℝ)) *
      normSq (BstLean.Part150.bT 12285 12285 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12285).tau0 c)) /
      (2 / (12285 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12285).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12285).tau0 c))⁻¹ •
      BstLean.Part150.bT 12285 12285 (A1 c) (A2 c) c.1.2 ((paperDesignP 12285).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12285 : ℝ)) * normSq (bR c) / (2 / (12285 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12285}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12285) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12285).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12285 : ℝ) * (paperDesignP 12285).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12285 12285 c.1.2 ((paperDesignP 12285).tau0 c) :=
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

end BstLean.Part262.Row12285

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12286
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12286 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12286).real (BstLean.Part211.CentreSource 12286 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12286) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12286 160 (6 / 1000)
  have hj := jS_160_le (n := 12286) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12286 160 (6 / 1000) ^ 2 * 12286 /
      (((12286 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12286 160 (6 / 1000) ^ 2 * 12286 /
      (((12286 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12286 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12286 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12286) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12286 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12286

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12286
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12286) :=
  Ethm (paperCentres 12286) ∩ Ethp (paperCentres 12286)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12286)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12286)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12286) (paperCentres 12286)
  have he : exp (-(45 / 10000 * (12286 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12286 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12286) :=
  (passEvent ∩ agentEv (paperDesignP 12286) (DirectionError 12286) ∩
    agentEv (paperDesignP 12286) (CentreSources 12286 12286)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12286)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12286) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12286) hτ
  have hC := centreSources_ret_charge_row 12286 (paperDesignP 12286) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12286)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12286) (CentreSources 12286 12286)
  direction : analyticBase ⊆ agentEv (paperDesignP 12286) (DirectionError 12286)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12286)) : Set (Ret 12286) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12286)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12286)}
    (hT : (retDist (paperCentres 12286)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12286)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12286)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12286)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12286)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12286)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12286

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12286
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12286 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12286 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12286 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12286 12286 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12286)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12286)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12286
  have hb0 := BstLean.Part150.betaJ_nonneg 12286
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12286 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12286 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12286 * BstLean.Part150.betaJ 12286) * 12286) ≤
      (31523091 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12286)) * 12286 := by gcongr <;> linarith
      _ ≤ ((31523091 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12286 * 12286 *
      (1 + BstLean.Part154.deltaChi 12286 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180409979 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12286 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180409979 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12286 : ℝ) / BstLean.Part154.csC) ≤ (12174333 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12286 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12174333 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12286 : ℝ) * (31523091 / 200000) +
        2 * (1792 / 10000 / 12286) * (180409979 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (12174333 / 125000) *
          (81 / 1000 / 12286 + (1792 / 10000 / 12286) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12286

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12286
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12286 ∧
    1 ≤ gPlus 12286 ∧ gPlus 12286 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12286 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12286 : ℝ) < √(1 - 2 / (12286 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12286 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12286 (gMinus 12286) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12286 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12286 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12286 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12286)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12286 (gMinus 12286) (gPlus 12286)
      (finiteEnergy 12286 12286 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12286 (gMinus 12286) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12286 (gMinus 12286) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12286 (gMinus 12286) (54 / 100))
    (by linarith : energyRatio 12286 (gMinus 12286) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12286 (gMinus 12286) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12286 * kappa (energyRatio 12286 (gMinus 12286) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12286) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12286 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12286 12286 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12286 12286 (11 / 1000) / √12286 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12286)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12286 * kappa (energyRatio 12286 (gMinus 12286) (54 / 100))) +
      2 * √(12 * gPlus 12286) / 12286 + finiteEnergy 12286 12286 (11 / 1000) / √12286 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12286 θ ∧ meanLowerRoot 12286 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12286 - 2 / (12286 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12286 - 2 / (12286 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12286 θ ^ 2 / gPlus 12286) - 2 / (12286 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12286 * (kappa (meanLowerRoot 12286 θ ^ 2 / gPlus 12286) -
        2 / (12286 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12286) / 12286 -
        finiteEnergy 12286 12286 (11 / 1000) / √12286 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12286 θ ^ 2 / gPlus 12286 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12286)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12286 θ ^ 2 / gPlus 12286 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12286)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12286 θ ^ 2 / gPlus 12286 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12286 ^ 2 ≤
      kappa (meanLowerRoot 12286 θ ^ 2 / gPlus 12286) - 2 / (12286 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12286 *
      (kappa (meanLowerRoot 12286 θ ^ 2 / gPlus 12286) - 2 / (12286 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12286 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12286)
    linarith
  have ht : √(12 * gPlus 12286) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12286 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12286 12286 (11 / 1000) / √12286 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12286)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12286 (gMinus 12286) (gPlus 12286)
      (finiteEnergy 12286 12286 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12286) (hτ : 0 < (paperDesignP 12286).tau0 c) :
    eR c = (2 / (mA 12286 : ℝ)) *
      normSq (BstLean.Part150.bT 12286 12286 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12286).tau0 c)) /
      (2 / (12286 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12286).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12286).tau0 c))⁻¹ •
      BstLean.Part150.bT 12286 12286 (A1 c) (A2 c) c.1.2 ((paperDesignP 12286).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12286 : ℝ)) * normSq (bR c) / (2 / (12286 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12286}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12286) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12286).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12286 : ℝ) * (paperDesignP 12286).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12286 12286 c.1.2 ((paperDesignP 12286).tau0 c) :=
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

end BstLean.Part262.Row12286

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12287
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12287 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12287).real (BstLean.Part211.CentreSource 12287 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12287) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12287 160 (6 / 1000)
  have hj := jS_160_le (n := 12287) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12287 160 (6 / 1000) ^ 2 * 12287 /
      (((12287 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12287 160 (6 / 1000) ^ 2 * 12287 /
      (((12287 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12287 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12287 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12287) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12287 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12287

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12287
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12287) :=
  Ethm (paperCentres 12287) ∩ Ethp (paperCentres 12287)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12287)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12287)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12287) (paperCentres 12287)
  have he : exp (-(45 / 10000 * (12287 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12287 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12287) :=
  (passEvent ∩ agentEv (paperDesignP 12287) (DirectionError 12287) ∩
    agentEv (paperDesignP 12287) (CentreSources 12287 12287)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12287)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12287) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12287) hτ
  have hC := centreSources_ret_charge_row 12287 (paperDesignP 12287) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12287)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12287) (CentreSources 12287 12287)
  direction : analyticBase ⊆ agentEv (paperDesignP 12287) (DirectionError 12287)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12287)) : Set (Ret 12287) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12287)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12287)}
    (hT : (retDist (paperCentres 12287)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12287)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12287)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12287)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12287)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12287)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12287

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12287
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12287 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12287 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12287 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12287 12287 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12287)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12287)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12287
  have hb0 := BstLean.Part150.betaJ_nonneg 12287
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12287 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12287 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12287 * BstLean.Part150.betaJ 12287) * 12287) ≤
      (157621869 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12287)) * 12287 := by gcongr <;> linarith
      _ ≤ ((157621869 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12287 * 12287 *
      (1 + BstLean.Part154.deltaChi 12287 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180417321 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12287 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180417321 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12287 : ℝ) / BstLean.Part154.csC) ≤ (97398627 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12287 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97398627 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12287 : ℝ) * (157621869 / 1000000) +
        2 * (1792 / 10000 / 12287) * (180417321 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97398627 / 1000000) *
          (81 / 1000 / 12287 + (1792 / 10000 / 12287) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12287

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12287
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12287 ∧
    1 ≤ gPlus 12287 ∧ gPlus 12287 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12287 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12287 : ℝ) < √(1 - 2 / (12287 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12287 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12287 (gMinus 12287) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12287 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12287 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12287 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12287)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12287 (gMinus 12287) (gPlus 12287)
      (finiteEnergy 12287 12287 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12287 (gMinus 12287) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12287 (gMinus 12287) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12287 (gMinus 12287) (54 / 100))
    (by linarith : energyRatio 12287 (gMinus 12287) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12287 (gMinus 12287) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12287 * kappa (energyRatio 12287 (gMinus 12287) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12287) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12287 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12287 12287 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12287 12287 (11 / 1000) / √12287 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12287)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12287 * kappa (energyRatio 12287 (gMinus 12287) (54 / 100))) +
      2 * √(12 * gPlus 12287) / 12287 + finiteEnergy 12287 12287 (11 / 1000) / √12287 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12287 θ ∧ meanLowerRoot 12287 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12287 - 2 / (12287 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12287 - 2 / (12287 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12287 θ ^ 2 / gPlus 12287) - 2 / (12287 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12287 * (kappa (meanLowerRoot 12287 θ ^ 2 / gPlus 12287) -
        2 / (12287 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12287) / 12287 -
        finiteEnergy 12287 12287 (11 / 1000) / √12287 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12287 θ ^ 2 / gPlus 12287 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12287)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12287 θ ^ 2 / gPlus 12287 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12287)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12287 θ ^ 2 / gPlus 12287 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12287 ^ 2 ≤
      kappa (meanLowerRoot 12287 θ ^ 2 / gPlus 12287) - 2 / (12287 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12287 *
      (kappa (meanLowerRoot 12287 θ ^ 2 / gPlus 12287) - 2 / (12287 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12287 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12287)
    linarith
  have ht : √(12 * gPlus 12287) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12287 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12287 12287 (11 / 1000) / √12287 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12287)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12287 (gMinus 12287) (gPlus 12287)
      (finiteEnergy 12287 12287 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12287) (hτ : 0 < (paperDesignP 12287).tau0 c) :
    eR c = (2 / (mA 12287 : ℝ)) *
      normSq (BstLean.Part150.bT 12287 12287 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12287).tau0 c)) /
      (2 / (12287 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12287).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12287).tau0 c))⁻¹ •
      BstLean.Part150.bT 12287 12287 (A1 c) (A2 c) c.1.2 ((paperDesignP 12287).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12287 : ℝ)) * normSq (bR c) / (2 / (12287 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12287}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12287) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12287).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12287 : ℝ) * (paperDesignP 12287).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12287 12287 c.1.2 ((paperDesignP 12287).tau0 c) :=
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

end BstLean.Part262.Row12287

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12288
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12288 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12288).real (BstLean.Part211.CentreSource 12288 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12288) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12288 160 (6 / 1000)
  have hj := jS_160_le (n := 12288) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12288 160 (6 / 1000) ^ 2 * 12288 /
      (((12288 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12288 160 (6 / 1000) ^ 2 * 12288 /
      (((12288 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12288 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12288 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12288) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12288 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12288

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12288
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12288) :=
  Ethm (paperCentres 12288) ∩ Ethp (paperCentres 12288)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12288)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12288)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12288) (paperCentres 12288)
  have he : exp (-(45 / 10000 * (12288 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12288 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12288) :=
  (passEvent ∩ agentEv (paperDesignP 12288) (DirectionError 12288) ∩
    agentEv (paperDesignP 12288) (CentreSources 12288 12288)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12288)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12288) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12288) hτ
  have hC := centreSources_ret_charge_row 12288 (paperDesignP 12288) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12288)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12288) (CentreSources 12288 12288)
  direction : analyticBase ⊆ agentEv (paperDesignP 12288) (DirectionError 12288)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12288)) : Set (Ret 12288) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12288)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12288)}
    (hT : (retDist (paperCentres 12288)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12288)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12288)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12288)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12288)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12288)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12288

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12288
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12288 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12288 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12288 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12288 12288 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12288)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12288)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12288
  have hb0 := BstLean.Part150.betaJ_nonneg 12288
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12288 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12288 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12288 * BstLean.Part150.betaJ 12288) * 12288) ≤
      (157628283 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12288)) * 12288 := by gcongr <;> linarith
      _ ≤ ((157628283 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12288 * 12288 *
      (1 + BstLean.Part154.deltaChi 12288 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180424663 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12288 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180424663 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12288 : ℝ) / BstLean.Part154.csC) ≤ (97402591 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12288 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97402591 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12288 : ℝ) * (157628283 / 1000000) +
        2 * (1792 / 10000 / 12288) * (180424663 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (97402591 / 1000000) *
          (81 / 1000 / 12288 + (1792 / 10000 / 12288) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12288

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12288
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12288 ∧
    1 ≤ gPlus 12288 ∧ gPlus 12288 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12288 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12288 : ℝ) < √(1 - 2 / (12288 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12288 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12288 (gMinus 12288) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12288 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12288 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12288 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12288)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12288 (gMinus 12288) (gPlus 12288)
      (finiteEnergy 12288 12288 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12288 (gMinus 12288) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12288 (gMinus 12288) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12288 (gMinus 12288) (54 / 100))
    (by linarith : energyRatio 12288 (gMinus 12288) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12288 (gMinus 12288) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12288 * kappa (energyRatio 12288 (gMinus 12288) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12288) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12288 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12288 12288 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12288 12288 (11 / 1000) / √12288 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12288)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12288 * kappa (energyRatio 12288 (gMinus 12288) (54 / 100))) +
      2 * √(12 * gPlus 12288) / 12288 + finiteEnergy 12288 12288 (11 / 1000) / √12288 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12288 θ ∧ meanLowerRoot 12288 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12288 - 2 / (12288 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12288 - 2 / (12288 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12288 θ ^ 2 / gPlus 12288) - 2 / (12288 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12288 * (kappa (meanLowerRoot 12288 θ ^ 2 / gPlus 12288) -
        2 / (12288 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12288) / 12288 -
        finiteEnergy 12288 12288 (11 / 1000) / √12288 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12288 θ ^ 2 / gPlus 12288 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12288)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12288 θ ^ 2 / gPlus 12288 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12288)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12288 θ ^ 2 / gPlus 12288 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12288 ^ 2 ≤
      kappa (meanLowerRoot 12288 θ ^ 2 / gPlus 12288) - 2 / (12288 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12288 *
      (kappa (meanLowerRoot 12288 θ ^ 2 / gPlus 12288) - 2 / (12288 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12288 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12288)
    linarith
  have ht : √(12 * gPlus 12288) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12288 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12288 12288 (11 / 1000) / √12288 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12288)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12288 (gMinus 12288) (gPlus 12288)
      (finiteEnergy 12288 12288 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12288) (hτ : 0 < (paperDesignP 12288).tau0 c) :
    eR c = (2 / (mA 12288 : ℝ)) *
      normSq (BstLean.Part150.bT 12288 12288 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12288).tau0 c)) /
      (2 / (12288 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12288).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12288).tau0 c))⁻¹ •
      BstLean.Part150.bT 12288 12288 (A1 c) (A2 c) c.1.2 ((paperDesignP 12288).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12288 : ℝ)) * normSq (bR c) / (2 / (12288 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12288}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12288) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12288).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12288 : ℝ) * (paperDesignP 12288).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12288 12288 c.1.2 ((paperDesignP 12288).tau0 c) :=
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

end BstLean.Part262.Row12288

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12289
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12289 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12289).real (BstLean.Part211.CentreSource 12289 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12289) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12289 160 (6 / 1000)
  have hj := jS_160_le (n := 12289) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12289 160 (6 / 1000) ^ 2 * 12289 /
      (((12289 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12289 160 (6 / 1000) ^ 2 * 12289 /
      (((12289 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12289 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12289 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12289) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12289 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12289

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12289
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12289) :=
  Ethm (paperCentres 12289) ∩ Ethp (paperCentres 12289)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12289)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12289)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12289) (paperCentres 12289)
  have he : exp (-(45 / 10000 * (12289 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12289 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12289) :=
  (passEvent ∩ agentEv (paperDesignP 12289) (DirectionError 12289) ∩
    agentEv (paperDesignP 12289) (CentreSources 12289 12289)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12289)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12289) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12289) hτ
  have hC := centreSources_ret_charge_row 12289 (paperDesignP 12289) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12289)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12289) (CentreSources 12289 12289)
  direction : analyticBase ⊆ agentEv (paperDesignP 12289) (DirectionError 12289)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12289)) : Set (Ret 12289) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12289)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12289)}
    (hT : (retDist (paperCentres 12289)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12289)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12289)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12289)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12289)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12289)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12289

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12289
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12289 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12289 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12289 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12289 12289 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12289)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12289)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12289
  have hb0 := BstLean.Part150.betaJ_nonneg 12289
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12289 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12289 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12289 * BstLean.Part150.betaJ 12289) * 12289) ≤
      (157634697 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12289)) * 12289 := by gcongr <;> linarith
      _ ≤ ((157634697 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12289 * 12289 *
      (1 + BstLean.Part154.deltaChi 12289 12 + 2 / π) / BstLean.Part154.csC) ≤
      (45108001 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12289 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((45108001 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12289 : ℝ) / BstLean.Part154.csC) ≤ (48703277 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12289 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48703277 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12289 : ℝ) * (157634697 / 1000000) +
        2 * (1792 / 10000 / 12289) * (45108001 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (48703277 / 500000) *
          (81 / 1000 / 12289 + (1792 / 10000 / 12289) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12289

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12289
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12289 ∧
    1 ≤ gPlus 12289 ∧ gPlus 12289 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12289 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12289 : ℝ) < √(1 - 2 / (12289 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12289 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12289 (gMinus 12289) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12289 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12289 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12289 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12289)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12289 (gMinus 12289) (gPlus 12289)
      (finiteEnergy 12289 12289 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12289 (gMinus 12289) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12289 (gMinus 12289) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12289 (gMinus 12289) (54 / 100))
    (by linarith : energyRatio 12289 (gMinus 12289) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12289 (gMinus 12289) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12289 * kappa (energyRatio 12289 (gMinus 12289) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12289) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12289 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12289 12289 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12289 12289 (11 / 1000) / √12289 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12289)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12289 * kappa (energyRatio 12289 (gMinus 12289) (54 / 100))) +
      2 * √(12 * gPlus 12289) / 12289 + finiteEnergy 12289 12289 (11 / 1000) / √12289 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12289 θ ∧ meanLowerRoot 12289 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12289 - 2 / (12289 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12289 - 2 / (12289 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12289 θ ^ 2 / gPlus 12289) - 2 / (12289 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12289 * (kappa (meanLowerRoot 12289 θ ^ 2 / gPlus 12289) -
        2 / (12289 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12289) / 12289 -
        finiteEnergy 12289 12289 (11 / 1000) / √12289 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12289 θ ^ 2 / gPlus 12289 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12289)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12289 θ ^ 2 / gPlus 12289 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12289)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12289 θ ^ 2 / gPlus 12289 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12289 ^ 2 ≤
      kappa (meanLowerRoot 12289 θ ^ 2 / gPlus 12289) - 2 / (12289 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12289 *
      (kappa (meanLowerRoot 12289 θ ^ 2 / gPlus 12289) - 2 / (12289 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12289 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12289)
    linarith
  have ht : √(12 * gPlus 12289) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12289 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12289 12289 (11 / 1000) / √12289 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12289)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12289 (gMinus 12289) (gPlus 12289)
      (finiteEnergy 12289 12289 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12289) (hτ : 0 < (paperDesignP 12289).tau0 c) :
    eR c = (2 / (mA 12289 : ℝ)) *
      normSq (BstLean.Part150.bT 12289 12289 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12289).tau0 c)) /
      (2 / (12289 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12289).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12289).tau0 c))⁻¹ •
      BstLean.Part150.bT 12289 12289 (A1 c) (A2 c) c.1.2 ((paperDesignP 12289).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12289 : ℝ)) * normSq (bR c) / (2 / (12289 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12289}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12289) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12289).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12289 : ℝ) * (paperDesignP 12289).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12289 12289 c.1.2 ((paperDesignP 12289).tau0 c) :=
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

end BstLean.Part262.Row12289

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12290
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12290 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12290).real (BstLean.Part211.CentreSource 12290 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12290) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12290 160 (6 / 1000)
  have hj := jS_160_le (n := 12290) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12290 160 (6 / 1000) ^ 2 * 12290 /
      (((12290 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12290 160 (6 / 1000) ^ 2 * 12290 /
      (((12290 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12290 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12290 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12290) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12290 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12290

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12290
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12290) :=
  Ethm (paperCentres 12290) ∩ Ethp (paperCentres 12290)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12290)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12290)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12290) (paperCentres 12290)
  have he : exp (-(45 / 10000 * (12290 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12290 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12290) :=
  (passEvent ∩ agentEv (paperDesignP 12290) (DirectionError 12290) ∩
    agentEv (paperDesignP 12290) (CentreSources 12290 12290)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12290)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12290) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12290) hτ
  have hC := centreSources_ret_charge_row 12290 (paperDesignP 12290) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12290)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12290) (CentreSources 12290 12290)
  direction : analyticBase ⊆ agentEv (paperDesignP 12290) (DirectionError 12290)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12290)) : Set (Ret 12290) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12290)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12290)}
    (hT : (retDist (paperCentres 12290)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12290)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12290)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12290)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12290)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12290)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12290

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12290
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12290 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12290 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12290 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12290 12290 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12290)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12290)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12290
  have hb0 := BstLean.Part150.betaJ_nonneg 12290
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12290 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12290 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12290 * BstLean.Part150.betaJ 12290) * 12290) ≤
      (15764111 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12290)) * 12290 := by gcongr <;> linarith
      _ ≤ ((15764111 / 100000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12290 * 12290 *
      (1 + BstLean.Part154.deltaChi 12290 12 + 2 / π) / BstLean.Part154.csC) ≤
      (36087869 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12290 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((36087869 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12290 : ℝ) / BstLean.Part154.csC) ≤ (97410517 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12290 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97410517 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12290 : ℝ) * (15764111 / 100000) +
        2 * (1792 / 10000 / 12290) * (36087869 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (97410517 / 1000000) *
          (81 / 1000 / 12290 + (1792 / 10000 / 12290) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12290

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12290
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12290 ∧
    1 ≤ gPlus 12290 ∧ gPlus 12290 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12290 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12290 : ℝ) < √(1 - 2 / (12290 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12290 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12290 (gMinus 12290) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12290 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12290 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12290 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12290)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12290 (gMinus 12290) (gPlus 12290)
      (finiteEnergy 12290 12290 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12290 (gMinus 12290) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12290 (gMinus 12290) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12290 (gMinus 12290) (54 / 100))
    (by linarith : energyRatio 12290 (gMinus 12290) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12290 (gMinus 12290) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12290 * kappa (energyRatio 12290 (gMinus 12290) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12290) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12290 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12290 12290 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12290 12290 (11 / 1000) / √12290 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12290)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12290 * kappa (energyRatio 12290 (gMinus 12290) (54 / 100))) +
      2 * √(12 * gPlus 12290) / 12290 + finiteEnergy 12290 12290 (11 / 1000) / √12290 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12290 θ ∧ meanLowerRoot 12290 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12290 - 2 / (12290 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12290 - 2 / (12290 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12290 θ ^ 2 / gPlus 12290) - 2 / (12290 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12290 * (kappa (meanLowerRoot 12290 θ ^ 2 / gPlus 12290) -
        2 / (12290 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12290) / 12290 -
        finiteEnergy 12290 12290 (11 / 1000) / √12290 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12290 θ ^ 2 / gPlus 12290 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12290)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12290 θ ^ 2 / gPlus 12290 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12290)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12290 θ ^ 2 / gPlus 12290 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12290 ^ 2 ≤
      kappa (meanLowerRoot 12290 θ ^ 2 / gPlus 12290) - 2 / (12290 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12290 *
      (kappa (meanLowerRoot 12290 θ ^ 2 / gPlus 12290) - 2 / (12290 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12290 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12290)
    linarith
  have ht : √(12 * gPlus 12290) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12290 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12290 12290 (11 / 1000) / √12290 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12290)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12290 (gMinus 12290) (gPlus 12290)
      (finiteEnergy 12290 12290 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12290) (hτ : 0 < (paperDesignP 12290).tau0 c) :
    eR c = (2 / (mA 12290 : ℝ)) *
      normSq (BstLean.Part150.bT 12290 12290 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12290).tau0 c)) /
      (2 / (12290 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12290).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12290).tau0 c))⁻¹ •
      BstLean.Part150.bT 12290 12290 (A1 c) (A2 c) c.1.2 ((paperDesignP 12290).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12290 : ℝ)) * normSq (bR c) / (2 / (12290 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12290}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12290) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12290).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12290 : ℝ) * (paperDesignP 12290).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12290 12290 c.1.2 ((paperDesignP 12290).tau0 c) :=
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

end BstLean.Part262.Row12290

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12291
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12291 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12291).real (BstLean.Part211.CentreSource 12291 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12291) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12291 160 (6 / 1000)
  have hj := jS_160_le (n := 12291) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12291 160 (6 / 1000) ^ 2 * 12291 /
      (((12291 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12291 160 (6 / 1000) ^ 2 * 12291 /
      (((12291 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12291 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12291 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12291) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12291 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12291

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12291
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12291) :=
  Ethm (paperCentres 12291) ∩ Ethp (paperCentres 12291)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12291)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12291)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12291) (paperCentres 12291)
  have he : exp (-(45 / 10000 * (12291 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12291 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12291) :=
  (passEvent ∩ agentEv (paperDesignP 12291) (DirectionError 12291) ∩
    agentEv (paperDesignP 12291) (CentreSources 12291 12291)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12291)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12291) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12291) hτ
  have hC := centreSources_ret_charge_row 12291 (paperDesignP 12291) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12291)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12291) (CentreSources 12291 12291)
  direction : analyticBase ⊆ agentEv (paperDesignP 12291) (DirectionError 12291)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12291)) : Set (Ret 12291) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12291)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12291)}
    (hT : (retDist (paperCentres 12291)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12291)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12291)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12291)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12291)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12291)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12291

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12291
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12291 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12291 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12291 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12291 12291 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12291)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12291)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12291
  have hb0 := BstLean.Part150.betaJ_nonneg 12291
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12291 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12291 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12291 * BstLean.Part150.betaJ 12291) * 12291) ≤
      (39411881 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12291)) * 12291 := by gcongr <;> linarith
      _ ≤ ((39411881 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12291 * 12291 *
      (1 + BstLean.Part154.deltaChi 12291 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90223343 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12291 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90223343 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12291 : ℝ) / BstLean.Part154.csC) ≤ (1217681 / 12500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12291 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((1217681 / 12500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12291 : ℝ) * (39411881 / 250000) +
        2 * (1792 / 10000 / 12291) * (90223343 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (1217681 / 12500) *
          (81 / 1000 / 12291 + (1792 / 10000 / 12291) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12291

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12291
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12291 ∧
    1 ≤ gPlus 12291 ∧ gPlus 12291 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12291 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12291 : ℝ) < √(1 - 2 / (12291 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12291 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12291 (gMinus 12291) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12291 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12291 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12291 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12291)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12291 (gMinus 12291) (gPlus 12291)
      (finiteEnergy 12291 12291 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12291 (gMinus 12291) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12291 (gMinus 12291) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12291 (gMinus 12291) (54 / 100))
    (by linarith : energyRatio 12291 (gMinus 12291) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12291 (gMinus 12291) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12291 * kappa (energyRatio 12291 (gMinus 12291) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12291) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12291 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12291 12291 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12291 12291 (11 / 1000) / √12291 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12291)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12291 * kappa (energyRatio 12291 (gMinus 12291) (54 / 100))) +
      2 * √(12 * gPlus 12291) / 12291 + finiteEnergy 12291 12291 (11 / 1000) / √12291 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12291 θ ∧ meanLowerRoot 12291 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12291 - 2 / (12291 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12291 - 2 / (12291 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12291 θ ^ 2 / gPlus 12291) - 2 / (12291 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12291 * (kappa (meanLowerRoot 12291 θ ^ 2 / gPlus 12291) -
        2 / (12291 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12291) / 12291 -
        finiteEnergy 12291 12291 (11 / 1000) / √12291 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12291 θ ^ 2 / gPlus 12291 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12291)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12291 θ ^ 2 / gPlus 12291 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12291)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12291 θ ^ 2 / gPlus 12291 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12291 ^ 2 ≤
      kappa (meanLowerRoot 12291 θ ^ 2 / gPlus 12291) - 2 / (12291 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12291 *
      (kappa (meanLowerRoot 12291 θ ^ 2 / gPlus 12291) - 2 / (12291 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12291 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12291)
    linarith
  have ht : √(12 * gPlus 12291) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12291 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12291 12291 (11 / 1000) / √12291 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12291)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12291 (gMinus 12291) (gPlus 12291)
      (finiteEnergy 12291 12291 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12291) (hτ : 0 < (paperDesignP 12291).tau0 c) :
    eR c = (2 / (mA 12291 : ℝ)) *
      normSq (BstLean.Part150.bT 12291 12291 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12291).tau0 c)) /
      (2 / (12291 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12291).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12291).tau0 c))⁻¹ •
      BstLean.Part150.bT 12291 12291 (A1 c) (A2 c) c.1.2 ((paperDesignP 12291).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12291 : ℝ)) * normSq (bR c) / (2 / (12291 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12291}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12291) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12291).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12291 : ℝ) * (paperDesignP 12291).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12291 12291 c.1.2 ((paperDesignP 12291).tau0 c) :=
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

end BstLean.Part262.Row12291

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12292
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12292 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12292).real (BstLean.Part211.CentreSource 12292 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12292) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12292 160 (6 / 1000)
  have hj := jS_160_le (n := 12292) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12292 160 (6 / 1000) ^ 2 * 12292 /
      (((12292 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12292 160 (6 / 1000) ^ 2 * 12292 /
      (((12292 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12292 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12292 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12292) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12292 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12292

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12292
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12292) :=
  Ethm (paperCentres 12292) ∩ Ethp (paperCentres 12292)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12292)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12292)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12292) (paperCentres 12292)
  have he : exp (-(45 / 10000 * (12292 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12292 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12292) :=
  (passEvent ∩ agentEv (paperDesignP 12292) (DirectionError 12292) ∩
    agentEv (paperDesignP 12292) (CentreSources 12292 12292)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12292)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12292) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12292) hτ
  have hC := centreSources_ret_charge_row 12292 (paperDesignP 12292) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12292)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12292) (CentreSources 12292 12292)
  direction : analyticBase ⊆ agentEv (paperDesignP 12292) (DirectionError 12292)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12292)) : Set (Ret 12292) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12292)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12292)}
    (hT : (retDist (paperCentres 12292)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12292)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12292)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12292)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12292)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12292)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12292

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12292
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12292 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12292 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12292 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12292 12292 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12292)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12292)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12292
  have hb0 := BstLean.Part150.betaJ_nonneg 12292
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12292 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12292 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12292 * BstLean.Part150.betaJ 12292) * 12292) ≤
      (9853371 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12292)) * 12292 := by gcongr <;> linarith
      _ ≤ ((9853371 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12292 * 12292 *
      (1 + BstLean.Part154.deltaChi 12292 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90227013 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12292 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90227013 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12292 : ℝ) / BstLean.Part154.csC) ≤ (97418443 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12292 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((97418443 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12292 : ℝ) * (9853371 / 62500) +
        2 * (1792 / 10000 / 12292) * (90227013 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (97418443 / 1000000) *
          (81 / 1000 / 12292 + (1792 / 10000 / 12292) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12292

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12292
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12292 ∧
    1 ≤ gPlus 12292 ∧ gPlus 12292 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12292 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12292 : ℝ) < √(1 - 2 / (12292 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12292 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12292 (gMinus 12292) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12292 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12292 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12292 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12292)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12292 (gMinus 12292) (gPlus 12292)
      (finiteEnergy 12292 12292 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12292 (gMinus 12292) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12292 (gMinus 12292) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12292 (gMinus 12292) (54 / 100))
    (by linarith : energyRatio 12292 (gMinus 12292) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12292 (gMinus 12292) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12292 * kappa (energyRatio 12292 (gMinus 12292) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12292) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12292 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12292 12292 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12292 12292 (11 / 1000) / √12292 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12292)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12292 * kappa (energyRatio 12292 (gMinus 12292) (54 / 100))) +
      2 * √(12 * gPlus 12292) / 12292 + finiteEnergy 12292 12292 (11 / 1000) / √12292 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12292 θ ∧ meanLowerRoot 12292 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12292 - 2 / (12292 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12292 - 2 / (12292 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12292 θ ^ 2 / gPlus 12292) - 2 / (12292 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12292 * (kappa (meanLowerRoot 12292 θ ^ 2 / gPlus 12292) -
        2 / (12292 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12292) / 12292 -
        finiteEnergy 12292 12292 (11 / 1000) / √12292 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12292 θ ^ 2 / gPlus 12292 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12292)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12292 θ ^ 2 / gPlus 12292 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12292)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12292 θ ^ 2 / gPlus 12292 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12292 ^ 2 ≤
      kappa (meanLowerRoot 12292 θ ^ 2 / gPlus 12292) - 2 / (12292 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12292 *
      (kappa (meanLowerRoot 12292 θ ^ 2 / gPlus 12292) - 2 / (12292 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12292 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12292)
    linarith
  have ht : √(12 * gPlus 12292) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12292 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12292 12292 (11 / 1000) / √12292 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12292)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12292 (gMinus 12292) (gPlus 12292)
      (finiteEnergy 12292 12292 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12292) (hτ : 0 < (paperDesignP 12292).tau0 c) :
    eR c = (2 / (mA 12292 : ℝ)) *
      normSq (BstLean.Part150.bT 12292 12292 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12292).tau0 c)) /
      (2 / (12292 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12292).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12292).tau0 c))⁻¹ •
      BstLean.Part150.bT 12292 12292 (A1 c) (A2 c) c.1.2 ((paperDesignP 12292).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12292 : ℝ)) * normSq (bR c) / (2 / (12292 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12292}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12292) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12292).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12292 : ℝ) * (paperDesignP 12292).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12292 12292 c.1.2 ((paperDesignP 12292).tau0 c) :=
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

end BstLean.Part262.Row12292

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12293
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12293 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12293).real (BstLean.Part211.CentreSource 12293 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12293) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12293 160 (6 / 1000)
  have hj := jS_160_le (n := 12293) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12293 160 (6 / 1000) ^ 2 * 12293 /
      (((12293 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12293 160 (6 / 1000) ^ 2 * 12293 /
      (((12293 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12293 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12293 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12293) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12293 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12293

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12293
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12293) :=
  Ethm (paperCentres 12293) ∩ Ethp (paperCentres 12293)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12293)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12293)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12293) (paperCentres 12293)
  have he : exp (-(45 / 10000 * (12293 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12293 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12293) :=
  (passEvent ∩ agentEv (paperDesignP 12293) (DirectionError 12293) ∩
    agentEv (paperDesignP 12293) (CentreSources 12293 12293)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12293)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12293) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12293) hτ
  have hC := centreSources_ret_charge_row 12293 (paperDesignP 12293) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12293)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12293) (CentreSources 12293 12293)
  direction : analyticBase ⊆ agentEv (paperDesignP 12293) (DirectionError 12293)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12293)) : Set (Ret 12293) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12293)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12293)}
    (hT : (retDist (paperCentres 12293)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12293)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12293)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12293)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12293)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12293)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12293

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12293
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12293 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12293 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12293 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12293 12293 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12293)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12293)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12293
  have hb0 := BstLean.Part150.betaJ_nonneg 12293
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12293 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12293 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12293 * BstLean.Part150.betaJ 12293) * 12293) ≤
      (157660349 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12293)) * 12293 := by gcongr <;> linarith
      _ ≤ ((157660349 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12293 * 12293 *
      (1 + BstLean.Part154.deltaChi 12293 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180461367 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12293 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180461367 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12293 : ℝ) / BstLean.Part154.csC) ≤ (19484481 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12293 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19484481 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12293 : ℝ) * (157660349 / 1000000) +
        2 * (1792 / 10000 / 12293) * (180461367 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (19484481 / 200000) *
          (81 / 1000 / 12293 + (1792 / 10000 / 12293) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12293

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12293
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12293 ∧
    1 ≤ gPlus 12293 ∧ gPlus 12293 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12293 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12293 : ℝ) < √(1 - 2 / (12293 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12293 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12293 (gMinus 12293) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12293 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12293 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12293 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12293)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12293 (gMinus 12293) (gPlus 12293)
      (finiteEnergy 12293 12293 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12293 (gMinus 12293) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12293 (gMinus 12293) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12293 (gMinus 12293) (54 / 100))
    (by linarith : energyRatio 12293 (gMinus 12293) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12293 (gMinus 12293) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12293 * kappa (energyRatio 12293 (gMinus 12293) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12293) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12293 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12293 12293 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12293 12293 (11 / 1000) / √12293 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12293)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12293 * kappa (energyRatio 12293 (gMinus 12293) (54 / 100))) +
      2 * √(12 * gPlus 12293) / 12293 + finiteEnergy 12293 12293 (11 / 1000) / √12293 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12293 θ ∧ meanLowerRoot 12293 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12293 - 2 / (12293 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12293 - 2 / (12293 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12293 θ ^ 2 / gPlus 12293) - 2 / (12293 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12293 * (kappa (meanLowerRoot 12293 θ ^ 2 / gPlus 12293) -
        2 / (12293 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12293) / 12293 -
        finiteEnergy 12293 12293 (11 / 1000) / √12293 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12293 θ ^ 2 / gPlus 12293 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12293)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12293 θ ^ 2 / gPlus 12293 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12293)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12293 θ ^ 2 / gPlus 12293 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12293 ^ 2 ≤
      kappa (meanLowerRoot 12293 θ ^ 2 / gPlus 12293) - 2 / (12293 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12293 *
      (kappa (meanLowerRoot 12293 θ ^ 2 / gPlus 12293) - 2 / (12293 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12293 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12293)
    linarith
  have ht : √(12 * gPlus 12293) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12293 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12293 12293 (11 / 1000) / √12293 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12293)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12293 (gMinus 12293) (gPlus 12293)
      (finiteEnergy 12293 12293 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12293) (hτ : 0 < (paperDesignP 12293).tau0 c) :
    eR c = (2 / (mA 12293 : ℝ)) *
      normSq (BstLean.Part150.bT 12293 12293 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12293).tau0 c)) /
      (2 / (12293 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12293).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12293).tau0 c))⁻¹ •
      BstLean.Part150.bT 12293 12293 (A1 c) (A2 c) c.1.2 ((paperDesignP 12293).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12293 : ℝ)) * normSq (bR c) / (2 / (12293 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12293}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12293) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12293).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12293 : ℝ) * (paperDesignP 12293).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12293 12293 c.1.2 ((paperDesignP 12293).tau0 c) :=
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

end BstLean.Part262.Row12293

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12294
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12294 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12294).real (BstLean.Part211.CentreSource 12294 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12294) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12294 160 (6 / 1000)
  have hj := jS_160_le (n := 12294) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12294 160 (6 / 1000) ^ 2 * 12294 /
      (((12294 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12294 160 (6 / 1000) ^ 2 * 12294 /
      (((12294 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12294 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12294 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12294) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12294 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12294

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12294
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12294) :=
  Ethm (paperCentres 12294) ∩ Ethp (paperCentres 12294)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12294)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12294)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12294) (paperCentres 12294)
  have he : exp (-(45 / 10000 * (12294 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12294 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12294) :=
  (passEvent ∩ agentEv (paperDesignP 12294) (DirectionError 12294) ∩
    agentEv (paperDesignP 12294) (CentreSources 12294 12294)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12294)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12294) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12294) hτ
  have hC := centreSources_ret_charge_row 12294 (paperDesignP 12294) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12294)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12294) (CentreSources 12294 12294)
  direction : analyticBase ⊆ agentEv (paperDesignP 12294) (DirectionError 12294)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12294)) : Set (Ret 12294) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12294)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12294)}
    (hT : (retDist (paperCentres 12294)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12294)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12294)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12294)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12294)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12294)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12294

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12294
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12294 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12294 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12294 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12294 12294 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12294)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12294)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12294
  have hb0 := BstLean.Part150.betaJ_nonneg 12294
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12294 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12294 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12294 * BstLean.Part150.betaJ 12294) * 12294) ≤
      (157666761 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12294)) * 12294 := by gcongr <;> linarith
      _ ≤ ((157666761 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12294 * 12294 *
      (1 + BstLean.Part154.deltaChi 12294 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90234353 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12294 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90234353 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12294 : ℝ) / BstLean.Part154.csC) ≤ (1522287 / 15625) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12294 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((1522287 / 15625) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12294 : ℝ) * (157666761 / 1000000) +
        2 * (1792 / 10000 / 12294) * (90234353 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (1522287 / 15625) *
          (81 / 1000 / 12294 + (1792 / 10000 / 12294) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12294

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12294
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12294 ∧
    1 ≤ gPlus 12294 ∧ gPlus 12294 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12294 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12294 : ℝ) < √(1 - 2 / (12294 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12294 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12294 (gMinus 12294) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12294 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12294 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12294 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12294)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12294 (gMinus 12294) (gPlus 12294)
      (finiteEnergy 12294 12294 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12294 (gMinus 12294) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12294 (gMinus 12294) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12294 (gMinus 12294) (54 / 100))
    (by linarith : energyRatio 12294 (gMinus 12294) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12294 (gMinus 12294) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12294 * kappa (energyRatio 12294 (gMinus 12294) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12294) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12294 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12294 12294 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12294 12294 (11 / 1000) / √12294 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12294)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12294 * kappa (energyRatio 12294 (gMinus 12294) (54 / 100))) +
      2 * √(12 * gPlus 12294) / 12294 + finiteEnergy 12294 12294 (11 / 1000) / √12294 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12294 θ ∧ meanLowerRoot 12294 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12294 - 2 / (12294 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12294 - 2 / (12294 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12294 θ ^ 2 / gPlus 12294) - 2 / (12294 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12294 * (kappa (meanLowerRoot 12294 θ ^ 2 / gPlus 12294) -
        2 / (12294 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12294) / 12294 -
        finiteEnergy 12294 12294 (11 / 1000) / √12294 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12294 θ ^ 2 / gPlus 12294 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12294)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12294 θ ^ 2 / gPlus 12294 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12294)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12294 θ ^ 2 / gPlus 12294 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12294 ^ 2 ≤
      kappa (meanLowerRoot 12294 θ ^ 2 / gPlus 12294) - 2 / (12294 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12294 *
      (kappa (meanLowerRoot 12294 θ ^ 2 / gPlus 12294) - 2 / (12294 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12294 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12294)
    linarith
  have ht : √(12 * gPlus 12294) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12294 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12294 12294 (11 / 1000) / √12294 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12294)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12294 (gMinus 12294) (gPlus 12294)
      (finiteEnergy 12294 12294 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12294) (hτ : 0 < (paperDesignP 12294).tau0 c) :
    eR c = (2 / (mA 12294 : ℝ)) *
      normSq (BstLean.Part150.bT 12294 12294 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12294).tau0 c)) /
      (2 / (12294 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12294).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12294).tau0 c))⁻¹ •
      BstLean.Part150.bT 12294 12294 (A1 c) (A2 c) c.1.2 ((paperDesignP 12294).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12294 : ℝ)) * normSq (bR c) / (2 / (12294 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12294}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12294) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12294).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12294 : ℝ) * (paperDesignP 12294).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12294 12294 c.1.2 ((paperDesignP 12294).tau0 c) :=
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

end BstLean.Part262.Row12294

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12295
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12295 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12295).real (BstLean.Part211.CentreSource 12295 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12295) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12295 160 (6 / 1000)
  have hj := jS_160_le (n := 12295) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12295 160 (6 / 1000) ^ 2 * 12295 /
      (((12295 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12295 160 (6 / 1000) ^ 2 * 12295 /
      (((12295 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12295 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12295 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12295) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12295 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12295

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12295
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12295) :=
  Ethm (paperCentres 12295) ∩ Ethp (paperCentres 12295)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12295)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12295)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12295) (paperCentres 12295)
  have he : exp (-(45 / 10000 * (12295 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12295 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12295) :=
  (passEvent ∩ agentEv (paperDesignP 12295) (DirectionError 12295) ∩
    agentEv (paperDesignP 12295) (CentreSources 12295 12295)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12295)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12295) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12295) hτ
  have hC := centreSources_ret_charge_row 12295 (paperDesignP 12295) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12295)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12295) (CentreSources 12295 12295)
  direction : analyticBase ⊆ agentEv (paperDesignP 12295) (DirectionError 12295)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12295)) : Set (Ret 12295) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12295)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12295)}
    (hT : (retDist (paperCentres 12295)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12295)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12295)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12295)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12295)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12295)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12295

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12295
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12295 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12295 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12295 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12295 12295 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12295)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12295)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12295
  have hb0 := BstLean.Part150.betaJ_nonneg 12295
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12295 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12295 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12295 * BstLean.Part150.betaJ 12295) * 12295) ≤
      (78836587 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12295)) * 12295 := by gcongr <;> linarith
      _ ≤ ((78836587 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12295 * 12295 *
      (1 + BstLean.Part154.deltaChi 12295 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90238023 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12295 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90238023 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12295 : ℝ) / BstLean.Part154.csC) ≤ (9743033 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12295 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((9743033 / 100000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12295 : ℝ) * (78836587 / 500000) +
        2 * (1792 / 10000 / 12295) * (90238023 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (9743033 / 100000) *
          (81 / 1000 / 12295 + (1792 / 10000 / 12295) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12295

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12295
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12295 ∧
    1 ≤ gPlus 12295 ∧ gPlus 12295 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12295 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12295 : ℝ) < √(1 - 2 / (12295 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12295 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12295 (gMinus 12295) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12295 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12295 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12295 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12295)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12295 (gMinus 12295) (gPlus 12295)
      (finiteEnergy 12295 12295 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12295 (gMinus 12295) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12295 (gMinus 12295) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12295 (gMinus 12295) (54 / 100))
    (by linarith : energyRatio 12295 (gMinus 12295) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12295 (gMinus 12295) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12295 * kappa (energyRatio 12295 (gMinus 12295) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12295) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12295 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12295 12295 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12295 12295 (11 / 1000) / √12295 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12295)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12295 * kappa (energyRatio 12295 (gMinus 12295) (54 / 100))) +
      2 * √(12 * gPlus 12295) / 12295 + finiteEnergy 12295 12295 (11 / 1000) / √12295 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12295 θ ∧ meanLowerRoot 12295 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12295 - 2 / (12295 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12295 - 2 / (12295 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12295 θ ^ 2 / gPlus 12295) - 2 / (12295 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12295 * (kappa (meanLowerRoot 12295 θ ^ 2 / gPlus 12295) -
        2 / (12295 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12295) / 12295 -
        finiteEnergy 12295 12295 (11 / 1000) / √12295 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12295 θ ^ 2 / gPlus 12295 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12295)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12295 θ ^ 2 / gPlus 12295 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12295)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12295 θ ^ 2 / gPlus 12295 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12295 ^ 2 ≤
      kappa (meanLowerRoot 12295 θ ^ 2 / gPlus 12295) - 2 / (12295 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12295 *
      (kappa (meanLowerRoot 12295 θ ^ 2 / gPlus 12295) - 2 / (12295 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12295 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12295)
    linarith
  have ht : √(12 * gPlus 12295) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12295 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12295 12295 (11 / 1000) / √12295 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12295)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12295 (gMinus 12295) (gPlus 12295)
      (finiteEnergy 12295 12295 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12295) (hτ : 0 < (paperDesignP 12295).tau0 c) :
    eR c = (2 / (mA 12295 : ℝ)) *
      normSq (BstLean.Part150.bT 12295 12295 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12295).tau0 c)) /
      (2 / (12295 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12295).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12295).tau0 c))⁻¹ •
      BstLean.Part150.bT 12295 12295 (A1 c) (A2 c) c.1.2 ((paperDesignP 12295).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12295 : ℝ)) * normSq (bR c) / (2 / (12295 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12295}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12295) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12295).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12295 : ℝ) * (paperDesignP 12295).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12295 12295 c.1.2 ((paperDesignP 12295).tau0 c) :=
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

end BstLean.Part262.Row12295

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12296
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12296 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12296).real (BstLean.Part211.CentreSource 12296 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12296) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12296 160 (6 / 1000)
  have hj := jS_160_le (n := 12296) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12296 160 (6 / 1000) ^ 2 * 12296 /
      (((12296 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12296 160 (6 / 1000) ^ 2 * 12296 /
      (((12296 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12296 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12296 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12296) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12296 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12296

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12296
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12296) :=
  Ethm (paperCentres 12296) ∩ Ethp (paperCentres 12296)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12296)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12296)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12296) (paperCentres 12296)
  have he : exp (-(45 / 10000 * (12296 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12296 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12296) :=
  (passEvent ∩ agentEv (paperDesignP 12296) (DirectionError 12296) ∩
    agentEv (paperDesignP 12296) (CentreSources 12296 12296)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12296)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12296) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12296) hτ
  have hC := centreSources_ret_charge_row 12296 (paperDesignP 12296) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12296)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12296) (CentreSources 12296 12296)
  direction : analyticBase ⊆ agentEv (paperDesignP 12296) (DirectionError 12296)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12296)) : Set (Ret 12296) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12296)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12296)}
    (hT : (retDist (paperCentres 12296)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12296)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12296)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12296)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12296)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12296)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12296

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12296
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12296 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12296 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12296 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12296 12296 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12296)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12296)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12296
  have hb0 := BstLean.Part150.betaJ_nonneg 12296
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12296 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12296 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12296 * BstLean.Part150.betaJ 12296) * 12296) ≤
      (31535917 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12296)) * 12296 := by gcongr <;> linarith
      _ ≤ ((31535917 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12296 * 12296 *
      (1 + BstLean.Part154.deltaChi 12296 12 + 2 / π) / BstLean.Part154.csC) ≤
      (36096677 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12296 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((36096677 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12296 : ℝ) / BstLean.Part154.csC) ≤ (24358573 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12296 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((24358573 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12296 : ℝ) * (31535917 / 200000) +
        2 * (1792 / 10000 / 12296) * (36096677 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (24358573 / 250000) *
          (81 / 1000 / 12296 + (1792 / 10000 / 12296) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12296

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12296
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12296 ∧
    1 ≤ gPlus 12296 ∧ gPlus 12296 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12296 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12296 : ℝ) < √(1 - 2 / (12296 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12296 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12296 (gMinus 12296) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12296 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12296 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12296 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12296)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12296 (gMinus 12296) (gPlus 12296)
      (finiteEnergy 12296 12296 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12296 (gMinus 12296) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12296 (gMinus 12296) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12296 (gMinus 12296) (54 / 100))
    (by linarith : energyRatio 12296 (gMinus 12296) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12296 (gMinus 12296) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12296 * kappa (energyRatio 12296 (gMinus 12296) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12296) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12296 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12296 12296 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12296 12296 (11 / 1000) / √12296 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12296)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12296 * kappa (energyRatio 12296 (gMinus 12296) (54 / 100))) +
      2 * √(12 * gPlus 12296) / 12296 + finiteEnergy 12296 12296 (11 / 1000) / √12296 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12296 θ ∧ meanLowerRoot 12296 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12296 - 2 / (12296 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12296 - 2 / (12296 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12296 θ ^ 2 / gPlus 12296) - 2 / (12296 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12296 * (kappa (meanLowerRoot 12296 θ ^ 2 / gPlus 12296) -
        2 / (12296 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12296) / 12296 -
        finiteEnergy 12296 12296 (11 / 1000) / √12296 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12296 θ ^ 2 / gPlus 12296 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12296)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12296 θ ^ 2 / gPlus 12296 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12296)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12296 θ ^ 2 / gPlus 12296 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12296 ^ 2 ≤
      kappa (meanLowerRoot 12296 θ ^ 2 / gPlus 12296) - 2 / (12296 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12296 *
      (kappa (meanLowerRoot 12296 θ ^ 2 / gPlus 12296) - 2 / (12296 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12296 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12296)
    linarith
  have ht : √(12 * gPlus 12296) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12296 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12296 12296 (11 / 1000) / √12296 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12296)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12296 (gMinus 12296) (gPlus 12296)
      (finiteEnergy 12296 12296 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12296) (hτ : 0 < (paperDesignP 12296).tau0 c) :
    eR c = (2 / (mA 12296 : ℝ)) *
      normSq (BstLean.Part150.bT 12296 12296 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12296).tau0 c)) /
      (2 / (12296 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12296).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12296).tau0 c))⁻¹ •
      BstLean.Part150.bT 12296 12296 (A1 c) (A2 c) c.1.2 ((paperDesignP 12296).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12296 : ℝ)) * normSq (bR c) / (2 / (12296 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12296}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12296) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12296).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12296 : ℝ) * (paperDesignP 12296).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12296 12296 c.1.2 ((paperDesignP 12296).tau0 c) :=
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

end BstLean.Part262.Row12296

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12297
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12297 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12297).real (BstLean.Part211.CentreSource 12297 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12297) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12297 160 (6 / 1000)
  have hj := jS_160_le (n := 12297) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12297 160 (6 / 1000) ^ 2 * 12297 /
      (((12297 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12297 160 (6 / 1000) ^ 2 * 12297 /
      (((12297 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12297 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12297 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12297) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12297 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12297

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12297
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12297) :=
  Ethm (paperCentres 12297) ∩ Ethp (paperCentres 12297)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12297)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12297)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12297) (paperCentres 12297)
  have he : exp (-(45 / 10000 * (12297 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12297 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12297) :=
  (passEvent ∩ agentEv (paperDesignP 12297) (DirectionError 12297) ∩
    agentEv (paperDesignP 12297) (CentreSources 12297 12297)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12297)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12297) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12297) hτ
  have hC := centreSources_ret_charge_row 12297 (paperDesignP 12297) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12297)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12297) (CentreSources 12297 12297)
  direction : analyticBase ⊆ agentEv (paperDesignP 12297) (DirectionError 12297)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12297)) : Set (Ret 12297) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12297)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12297)}
    (hT : (retDist (paperCentres 12297)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12297)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12297)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12297)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12297)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12297)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12297

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12297
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12297 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12297 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12297 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12297 12297 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12297)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12297)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12297
  have hb0 := BstLean.Part150.betaJ_nonneg 12297
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12297 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12297 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12297 * BstLean.Part150.betaJ 12297) * 12297) ≤
      (157685997 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12297)) * 12297 := by gcongr <;> linarith
      _ ≤ ((157685997 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12297 * 12297 *
      (1 + BstLean.Part154.deltaChi 12297 12 + 2 / π) / BstLean.Part154.csC) ≤
      (45122681 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12297 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((45122681 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12297 : ℝ) / BstLean.Part154.csC) ≤ (48719127 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12297 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48719127 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12297 : ℝ) * (157685997 / 1000000) +
        2 * (1792 / 10000 / 12297) * (45122681 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (48719127 / 500000) *
          (81 / 1000 / 12297 + (1792 / 10000 / 12297) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12297

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12297
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12297 ∧
    1 ≤ gPlus 12297 ∧ gPlus 12297 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12297 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12297 : ℝ) < √(1 - 2 / (12297 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12297 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12297 (gMinus 12297) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12297 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12297 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12297 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12297)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12297 (gMinus 12297) (gPlus 12297)
      (finiteEnergy 12297 12297 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12297 (gMinus 12297) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12297 (gMinus 12297) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12297 (gMinus 12297) (54 / 100))
    (by linarith : energyRatio 12297 (gMinus 12297) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12297 (gMinus 12297) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12297 * kappa (energyRatio 12297 (gMinus 12297) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12297) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12297 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12297 12297 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12297 12297 (11 / 1000) / √12297 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12297)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12297 * kappa (energyRatio 12297 (gMinus 12297) (54 / 100))) +
      2 * √(12 * gPlus 12297) / 12297 + finiteEnergy 12297 12297 (11 / 1000) / √12297 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12297 θ ∧ meanLowerRoot 12297 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12297 - 2 / (12297 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12297 - 2 / (12297 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12297 θ ^ 2 / gPlus 12297) - 2 / (12297 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12297 * (kappa (meanLowerRoot 12297 θ ^ 2 / gPlus 12297) -
        2 / (12297 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12297) / 12297 -
        finiteEnergy 12297 12297 (11 / 1000) / √12297 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12297 θ ^ 2 / gPlus 12297 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12297)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12297 θ ^ 2 / gPlus 12297 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12297)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12297 θ ^ 2 / gPlus 12297 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12297 ^ 2 ≤
      kappa (meanLowerRoot 12297 θ ^ 2 / gPlus 12297) - 2 / (12297 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12297 *
      (kappa (meanLowerRoot 12297 θ ^ 2 / gPlus 12297) - 2 / (12297 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12297 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12297)
    linarith
  have ht : √(12 * gPlus 12297) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12297 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12297 12297 (11 / 1000) / √12297 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12297)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12297 (gMinus 12297) (gPlus 12297)
      (finiteEnergy 12297 12297 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12297) (hτ : 0 < (paperDesignP 12297).tau0 c) :
    eR c = (2 / (mA 12297 : ℝ)) *
      normSq (BstLean.Part150.bT 12297 12297 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12297).tau0 c)) /
      (2 / (12297 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12297).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12297).tau0 c))⁻¹ •
      BstLean.Part150.bT 12297 12297 (A1 c) (A2 c) c.1.2 ((paperDesignP 12297).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12297 : ℝ)) * normSq (bR c) / (2 / (12297 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12297}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12297) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12297).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12297 : ℝ) * (paperDesignP 12297).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12297 12297 c.1.2 ((paperDesignP 12297).tau0 c) :=
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

end BstLean.Part262.Row12297

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12298
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12298 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12298).real (BstLean.Part211.CentreSource 12298 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12298) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12298 160 (6 / 1000)
  have hj := jS_160_le (n := 12298) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12298 160 (6 / 1000) ^ 2 * 12298 /
      (((12298 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12298 160 (6 / 1000) ^ 2 * 12298 /
      (((12298 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12298 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12298 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12298) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12298 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12298

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12298
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12298) :=
  Ethm (paperCentres 12298) ∩ Ethp (paperCentres 12298)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12298)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12298)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12298) (paperCentres 12298)
  have he : exp (-(45 / 10000 * (12298 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12298 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12298) :=
  (passEvent ∩ agentEv (paperDesignP 12298) (DirectionError 12298) ∩
    agentEv (paperDesignP 12298) (CentreSources 12298 12298)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12298)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12298) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12298) hτ
  have hC := centreSources_ret_charge_row 12298 (paperDesignP 12298) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12298)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12298) (CentreSources 12298 12298)
  direction : analyticBase ⊆ agentEv (paperDesignP 12298) (DirectionError 12298)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12298)) : Set (Ret 12298) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12298)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12298)}
    (hT : (retDist (paperCentres 12298)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12298)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12298)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12298)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12298)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12298)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12298

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12298
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12298 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12298 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12298 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12298 12298 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12298)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12298)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12298
  have hb0 := BstLean.Part150.betaJ_nonneg 12298
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12298 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12298 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12298 * BstLean.Part150.betaJ 12298) * 12298) ≤
      (19711551 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12298)) * 12298 := by gcongr <;> linarith
      _ ≤ ((19711551 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12298 * 12298 *
      (1 + BstLean.Part154.deltaChi 12298 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180498063 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12298 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180498063 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12298 : ℝ) / BstLean.Part154.csC) ≤ (12180277 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12298 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12180277 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12298 : ℝ) * (19711551 / 125000) +
        2 * (1792 / 10000 / 12298) * (180498063 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (12180277 / 125000) *
          (81 / 1000 / 12298 + (1792 / 10000 / 12298) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12298

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12298
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12298 ∧
    1 ≤ gPlus 12298 ∧ gPlus 12298 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12298 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12298 : ℝ) < √(1 - 2 / (12298 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12298 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12298 (gMinus 12298) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12298 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12298 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12298 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12298)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12298 (gMinus 12298) (gPlus 12298)
      (finiteEnergy 12298 12298 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12298 (gMinus 12298) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12298 (gMinus 12298) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12298 (gMinus 12298) (54 / 100))
    (by linarith : energyRatio 12298 (gMinus 12298) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12298 (gMinus 12298) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12298 * kappa (energyRatio 12298 (gMinus 12298) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12298) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12298 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12298 12298 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12298 12298 (11 / 1000) / √12298 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12298)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12298 * kappa (energyRatio 12298 (gMinus 12298) (54 / 100))) +
      2 * √(12 * gPlus 12298) / 12298 + finiteEnergy 12298 12298 (11 / 1000) / √12298 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12298 θ ∧ meanLowerRoot 12298 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12298 - 2 / (12298 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12298 - 2 / (12298 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12298 θ ^ 2 / gPlus 12298) - 2 / (12298 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12298 * (kappa (meanLowerRoot 12298 θ ^ 2 / gPlus 12298) -
        2 / (12298 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12298) / 12298 -
        finiteEnergy 12298 12298 (11 / 1000) / √12298 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12298 θ ^ 2 / gPlus 12298 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12298)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12298 θ ^ 2 / gPlus 12298 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12298)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12298 θ ^ 2 / gPlus 12298 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12298 ^ 2 ≤
      kappa (meanLowerRoot 12298 θ ^ 2 / gPlus 12298) - 2 / (12298 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12298 *
      (kappa (meanLowerRoot 12298 θ ^ 2 / gPlus 12298) - 2 / (12298 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12298 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12298)
    linarith
  have ht : √(12 * gPlus 12298) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12298 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12298 12298 (11 / 1000) / √12298 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12298)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12298 (gMinus 12298) (gPlus 12298)
      (finiteEnergy 12298 12298 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12298) (hτ : 0 < (paperDesignP 12298).tau0 c) :
    eR c = (2 / (mA 12298 : ℝ)) *
      normSq (BstLean.Part150.bT 12298 12298 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12298).tau0 c)) /
      (2 / (12298 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12298).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12298).tau0 c))⁻¹ •
      BstLean.Part150.bT 12298 12298 (A1 c) (A2 c) c.1.2 ((paperDesignP 12298).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12298 : ℝ)) * normSq (bR c) / (2 / (12298 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12298}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12298) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12298).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12298 : ℝ) * (paperDesignP 12298).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12298 12298 c.1.2 ((paperDesignP 12298).tau0 c) :=
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

end BstLean.Part262.Row12298

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part262.Row12299
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12299 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12299).real (BstLean.Part211.CentreSource 12299 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12299) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12299 160 (6 / 1000)
  have hj := jS_160_le (n := 12299) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12299 160 (6 / 1000) ^ 2 * 12299 /
      (((12299 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12299 160 (6 / 1000) ^ 2 * 12299 /
      (((12299 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12299 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12299 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12299) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12299 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part262.Row12299

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part262.Row12299
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12299) :=
  Ethm (paperCentres 12299) ∩ Ethp (paperCentres 12299)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12299)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12299)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12299) (paperCentres 12299)
  have he : exp (-(45 / 10000 * (12299 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12299 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12299) :=
  (passEvent ∩ agentEv (paperDesignP 12299) (DirectionError 12299) ∩
    agentEv (paperDesignP 12299) (CentreSources 12299 12299)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12299)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12299) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12299) hτ
  have hC := centreSources_ret_charge_row 12299 (paperDesignP 12299) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12299)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12299) (CentreSources 12299 12299)
  direction : analyticBase ⊆ agentEv (paperDesignP 12299) (DirectionError 12299)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12299)) : Set (Ret 12299) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12299)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12299)}
    (hT : (retDist (paperCentres 12299)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12299)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12299)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12299)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12299)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12299)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part262.Row12299

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part262.Row12299
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12299 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12299 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12299 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12299 12299 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12299)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12299)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12299
  have hb0 := BstLean.Part150.betaJ_nonneg 12299
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12299 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12299 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12299 * BstLean.Part150.betaJ 12299) * 12299) ≤
      (7884941 / 50000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12299)) * 12299 := by gcongr <;> linarith
      _ ≤ ((7884941 / 50000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12299 * 12299 *
      (1 + BstLean.Part154.deltaChi 12299 12 + 2 / π) / BstLean.Part154.csC) ≤
      (180505401 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12299 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((180505401 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12299 : ℝ) / BstLean.Part154.csC) ≤ (48723089 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12299 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((48723089 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12299 : ℝ) * (7884941 / 50000) +
        2 * (1792 / 10000 / 12299) * (180505401 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (48723089 / 500000) *
          (81 / 1000 / 12299 + (1792 / 10000 / 12299) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part262.Row12299

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part262.Row12299
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12299 ∧
    1 ≤ gPlus 12299 ∧ gPlus 12299 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12299 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12299 : ℝ) < √(1 - 2 / (12299 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12299 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12299 (gMinus 12299) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12299 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12299 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12299 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12299)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12299 (gMinus 12299) (gPlus 12299)
      (finiteEnergy 12299 12299 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12299 (gMinus 12299) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12299 (gMinus 12299) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12299 (gMinus 12299) (54 / 100))
    (by linarith : energyRatio 12299 (gMinus 12299) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12299 (gMinus 12299) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12299 * kappa (energyRatio 12299 (gMinus 12299) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12299) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12299 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12299 12299 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12299 12299 (11 / 1000) / √12299 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12299)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12299 * kappa (energyRatio 12299 (gMinus 12299) (54 / 100))) +
      2 * √(12 * gPlus 12299) / 12299 + finiteEnergy 12299 12299 (11 / 1000) / √12299 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12299 θ ∧ meanLowerRoot 12299 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12299 - 2 / (12299 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12299 - 2 / (12299 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12299 θ ^ 2 / gPlus 12299) - 2 / (12299 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12299 * (kappa (meanLowerRoot 12299 θ ^ 2 / gPlus 12299) -
        2 / (12299 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12299) / 12299 -
        finiteEnergy 12299 12299 (11 / 1000) / √12299 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12299 θ ^ 2 / gPlus 12299 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12299)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12299 θ ^ 2 / gPlus 12299 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12299)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12299 θ ^ 2 / gPlus 12299 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12299 ^ 2 ≤
      kappa (meanLowerRoot 12299 θ ^ 2 / gPlus 12299) - 2 / (12299 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12299 *
      (kappa (meanLowerRoot 12299 θ ^ 2 / gPlus 12299) - 2 / (12299 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12299 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12299)
    linarith
  have ht : √(12 * gPlus 12299) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12299 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12299 12299 (11 / 1000) / √12299 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12299)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12299 (gMinus 12299) (gPlus 12299)
      (finiteEnergy 12299 12299 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12299) (hτ : 0 < (paperDesignP 12299).tau0 c) :
    eR c = (2 / (mA 12299 : ℝ)) *
      normSq (BstLean.Part150.bT 12299 12299 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12299).tau0 c)) /
      (2 / (12299 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12299).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12299).tau0 c))⁻¹ •
      BstLean.Part150.bT 12299 12299 (A1 c) (A2 c) c.1.2 ((paperDesignP 12299).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12299 : ℝ)) * normSq (bR c) / (2 / (12299 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12299}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12299) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12299).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12299 : ℝ) * (paperDesignP 12299).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12299 12299 c.1.2 ((paperDesignP 12299).tau0 c) :=
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

end BstLean.Part262.Row12299
