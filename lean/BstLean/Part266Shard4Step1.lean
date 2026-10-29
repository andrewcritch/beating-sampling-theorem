import BstLean.Part266Shard4Step0


/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12450 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12450).real (BstLean.Part211.CentreSource 12450 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12450) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12450 160 (6 / 1000)
  have hj := jS_160_le (n := 12450) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12450 160 (6 / 1000) ^ 2 * 12450 /
      (((12450 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12450 160 (6 / 1000) ^ 2 * 12450 /
      (((12450 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12450 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12450 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12450) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12450 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12450

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12450) :=
  Ethm (paperCentres 12450) ∩ Ethp (paperCentres 12450)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12450)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12450)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12450) (paperCentres 12450)
  have he : exp (-(45 / 10000 * (12450 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12450 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12450) :=
  (passEvent ∩ agentEv (paperDesignP 12450) (DirectionError 12450) ∩
    agentEv (paperDesignP 12450) (CentreSources 12450 12450)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12450)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12450) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12450) hτ
  have hC := centreSources_ret_charge_row 12450 (paperDesignP 12450) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12450)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12450) (CentreSources 12450 12450)
  direction : analyticBase ⊆ agentEv (paperDesignP 12450) (DirectionError 12450)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12450)) : Set (Ret 12450) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12450)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12450)}
    (hT : (retDist (paperCentres 12450)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12450)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12450)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12450)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12450)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12450)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12450

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12450 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12450 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12450 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12450 12450 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12450)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12450)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12450
  have hb0 := BstLean.Part150.betaJ_nonneg 12450
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12450 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12450 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12450 * BstLean.Part150.betaJ 12450) * 12450) ≤
      (158663921 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12450)) * 12450 := by gcongr <;> linarith
      _ ≤ ((158663921 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12450 * 12450 *
      (1 + BstLean.Part154.deltaChi 12450 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181610091 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12450 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181610091 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12450 : ℝ) / BstLean.Part154.csC) ≤ (98042547 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12450 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98042547 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12450 : ℝ) * (158663921 / 1000000) +
        2 * (1792 / 10000 / 12450) * (181610091 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (98042547 / 1000000) *
          (81 / 1000 / 12450 + (1792 / 10000 / 12450) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12450

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12450
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12450 ∧
    1 ≤ gPlus 12450 ∧ gPlus 12450 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12450 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12450 : ℝ) < √(1 - 2 / (12450 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12450 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12450 (gMinus 12450) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12450 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12450 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12450 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12450)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12450 (gMinus 12450) (gPlus 12450)
      (finiteEnergy 12450 12450 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12450 (gMinus 12450) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12450 (gMinus 12450) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12450 (gMinus 12450) (54 / 100))
    (by linarith : energyRatio 12450 (gMinus 12450) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12450 (gMinus 12450) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12450 * kappa (energyRatio 12450 (gMinus 12450) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12450) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12450 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12450 12450 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12450 12450 (11 / 1000) / √12450 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12450)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12450 * kappa (energyRatio 12450 (gMinus 12450) (54 / 100))) +
      2 * √(12 * gPlus 12450) / 12450 + finiteEnergy 12450 12450 (11 / 1000) / √12450 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12450 θ ∧ meanLowerRoot 12450 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12450 - 2 / (12450 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12450 - 2 / (12450 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12450 θ ^ 2 / gPlus 12450) - 2 / (12450 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12450 * (kappa (meanLowerRoot 12450 θ ^ 2 / gPlus 12450) -
        2 / (12450 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12450) / 12450 -
        finiteEnergy 12450 12450 (11 / 1000) / √12450 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12450 θ ^ 2 / gPlus 12450 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12450)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12450 θ ^ 2 / gPlus 12450 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12450)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12450 θ ^ 2 / gPlus 12450 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12450 ^ 2 ≤
      kappa (meanLowerRoot 12450 θ ^ 2 / gPlus 12450) - 2 / (12450 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12450 *
      (kappa (meanLowerRoot 12450 θ ^ 2 / gPlus 12450) - 2 / (12450 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12450 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12450)
    linarith
  have ht : √(12 * gPlus 12450) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12450 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12450 12450 (11 / 1000) / √12450 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12450)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12450 (gMinus 12450) (gPlus 12450)
      (finiteEnergy 12450 12450 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12450) (hτ : 0 < (paperDesignP 12450).tau0 c) :
    eR c = (2 / (mA 12450 : ℝ)) *
      normSq (BstLean.Part150.bT 12450 12450 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12450).tau0 c)) /
      (2 / (12450 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12450).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12450).tau0 c))⁻¹ •
      BstLean.Part150.bT 12450 12450 (A1 c) (A2 c) c.1.2 ((paperDesignP 12450).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12450 : ℝ)) * normSq (bR c) / (2 / (12450 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12450}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12450) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12450).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12450 : ℝ) * (paperDesignP 12450).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12450 12450 c.1.2 ((paperDesignP 12450).tau0 c) :=
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

end BstLean.Part266.Row12450

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12451 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12451).real (BstLean.Part211.CentreSource 12451 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12451) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12451 160 (6 / 1000)
  have hj := jS_160_le (n := 12451) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12451 160 (6 / 1000) ^ 2 * 12451 /
      (((12451 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12451 160 (6 / 1000) ^ 2 * 12451 /
      (((12451 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12451 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12451 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12451) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12451 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12451

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12451) :=
  Ethm (paperCentres 12451) ∩ Ethp (paperCentres 12451)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12451)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12451)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12451) (paperCentres 12451)
  have he : exp (-(45 / 10000 * (12451 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12451 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12451) :=
  (passEvent ∩ agentEv (paperDesignP 12451) (DirectionError 12451) ∩
    agentEv (paperDesignP 12451) (CentreSources 12451 12451)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12451)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12451) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12451) hτ
  have hC := centreSources_ret_charge_row 12451 (paperDesignP 12451) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12451)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12451) (CentreSources 12451 12451)
  direction : analyticBase ⊆ agentEv (paperDesignP 12451) (DirectionError 12451)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12451)) : Set (Ret 12451) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12451)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12451)}
    (hT : (retDist (paperCentres 12451)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12451)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12451)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12451)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12451)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12451)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12451

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12451 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12451 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12451 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12451 12451 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12451)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12451)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12451
  have hb0 := BstLean.Part150.betaJ_nonneg 12451
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12451 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12451 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12451 * BstLean.Part150.betaJ 12451) * 12451) ≤
      (39667573 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12451)) * 12451 := by gcongr <;> linarith
      _ ≤ ((39667573 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12451 * 12451 *
      (1 + BstLean.Part154.deltaChi 12451 12 + 2 / π) / BstLean.Part154.csC) ≤
      (36323477 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12451 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((36323477 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12451 : ℝ) / BstLean.Part154.csC) ≤ (24511621 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12451 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((24511621 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12451 : ℝ) * (39667573 / 250000) +
        2 * (1792 / 10000 / 12451) * (36323477 / 200000) +
        4 * (1 / 2.506628) * 1.036505 * (24511621 / 250000) *
          (81 / 1000 / 12451 + (1792 / 10000 / 12451) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12451

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12451
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12451 ∧
    1 ≤ gPlus 12451 ∧ gPlus 12451 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12451 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12451 : ℝ) < √(1 - 2 / (12451 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12451 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12451 (gMinus 12451) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12451 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12451 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12451 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12451)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12451 (gMinus 12451) (gPlus 12451)
      (finiteEnergy 12451 12451 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12451 (gMinus 12451) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12451 (gMinus 12451) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12451 (gMinus 12451) (54 / 100))
    (by linarith : energyRatio 12451 (gMinus 12451) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12451 (gMinus 12451) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12451 * kappa (energyRatio 12451 (gMinus 12451) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12451) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12451 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12451 12451 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12451 12451 (11 / 1000) / √12451 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12451)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12451 * kappa (energyRatio 12451 (gMinus 12451) (54 / 100))) +
      2 * √(12 * gPlus 12451) / 12451 + finiteEnergy 12451 12451 (11 / 1000) / √12451 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12451 θ ∧ meanLowerRoot 12451 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12451 - 2 / (12451 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12451 - 2 / (12451 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12451 θ ^ 2 / gPlus 12451) - 2 / (12451 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12451 * (kappa (meanLowerRoot 12451 θ ^ 2 / gPlus 12451) -
        2 / (12451 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12451) / 12451 -
        finiteEnergy 12451 12451 (11 / 1000) / √12451 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12451 θ ^ 2 / gPlus 12451 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12451)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12451 θ ^ 2 / gPlus 12451 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12451)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12451 θ ^ 2 / gPlus 12451 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12451 ^ 2 ≤
      kappa (meanLowerRoot 12451 θ ^ 2 / gPlus 12451) - 2 / (12451 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12451 *
      (kappa (meanLowerRoot 12451 θ ^ 2 / gPlus 12451) - 2 / (12451 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12451 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12451)
    linarith
  have ht : √(12 * gPlus 12451) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12451 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12451 12451 (11 / 1000) / √12451 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12451)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12451 (gMinus 12451) (gPlus 12451)
      (finiteEnergy 12451 12451 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12451) (hτ : 0 < (paperDesignP 12451).tau0 c) :
    eR c = (2 / (mA 12451 : ℝ)) *
      normSq (BstLean.Part150.bT 12451 12451 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12451).tau0 c)) /
      (2 / (12451 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12451).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12451).tau0 c))⁻¹ •
      BstLean.Part150.bT 12451 12451 (A1 c) (A2 c) c.1.2 ((paperDesignP 12451).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12451 : ℝ)) * normSq (bR c) / (2 / (12451 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12451}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12451) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12451).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12451 : ℝ) * (paperDesignP 12451).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12451 12451 c.1.2 ((paperDesignP 12451).tau0 c) :=
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

end BstLean.Part266.Row12451

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12452 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12452).real (BstLean.Part211.CentreSource 12452 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12452) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12452 160 (6 / 1000)
  have hj := jS_160_le (n := 12452) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12452 160 (6 / 1000) ^ 2 * 12452 /
      (((12452 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12452 160 (6 / 1000) ^ 2 * 12452 /
      (((12452 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12452 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12452 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12452) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12452 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12452

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12452) :=
  Ethm (paperCentres 12452) ∩ Ethp (paperCentres 12452)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12452)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12452)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12452) (paperCentres 12452)
  have he : exp (-(45 / 10000 * (12452 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12452 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12452) :=
  (passEvent ∩ agentEv (paperDesignP 12452) (DirectionError 12452) ∩
    agentEv (paperDesignP 12452) (CentreSources 12452 12452)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12452)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12452) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12452) hτ
  have hC := centreSources_ret_charge_row 12452 (paperDesignP 12452) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12452)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12452) (CentreSources 12452 12452)
  direction : analyticBase ⊆ agentEv (paperDesignP 12452) (DirectionError 12452)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12452)) : Set (Ret 12452) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12452)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12452)}
    (hT : (retDist (paperCentres 12452)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12452)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12452)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12452)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12452)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12452)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12452

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12452 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12452 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12452 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12452 12452 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12452)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12452)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12452
  have hb0 := BstLean.Part150.betaJ_nonneg 12452
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12452 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12452 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12452 * BstLean.Part150.betaJ 12452) * 12452) ≤
      (19834583 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12452)) * 12452 := by gcongr <;> linarith
      _ ≤ ((19834583 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12452 * 12452 *
      (1 + BstLean.Part154.deltaChi 12452 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90812339 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12452 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90812339 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12452 : ℝ) / BstLean.Part154.csC) ≤ (98050421 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12452 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98050421 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12452 : ℝ) * (19834583 / 125000) +
        2 * (1792 / 10000 / 12452) * (90812339 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (98050421 / 1000000) *
          (81 / 1000 / 12452 + (1792 / 10000 / 12452) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12452

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12452
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12452 ∧
    1 ≤ gPlus 12452 ∧ gPlus 12452 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12452 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12452 : ℝ) < √(1 - 2 / (12452 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12452 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12452 (gMinus 12452) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12452 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12452 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12452 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12452)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12452 (gMinus 12452) (gPlus 12452)
      (finiteEnergy 12452 12452 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12452 (gMinus 12452) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12452 (gMinus 12452) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12452 (gMinus 12452) (54 / 100))
    (by linarith : energyRatio 12452 (gMinus 12452) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12452 (gMinus 12452) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12452 * kappa (energyRatio 12452 (gMinus 12452) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12452) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12452 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12452 12452 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12452 12452 (11 / 1000) / √12452 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12452)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12452 * kappa (energyRatio 12452 (gMinus 12452) (54 / 100))) +
      2 * √(12 * gPlus 12452) / 12452 + finiteEnergy 12452 12452 (11 / 1000) / √12452 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12452 θ ∧ meanLowerRoot 12452 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12452 - 2 / (12452 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12452 - 2 / (12452 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12452 θ ^ 2 / gPlus 12452) - 2 / (12452 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12452 * (kappa (meanLowerRoot 12452 θ ^ 2 / gPlus 12452) -
        2 / (12452 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12452) / 12452 -
        finiteEnergy 12452 12452 (11 / 1000) / √12452 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12452 θ ^ 2 / gPlus 12452 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12452)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12452 θ ^ 2 / gPlus 12452 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12452)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12452 θ ^ 2 / gPlus 12452 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12452 ^ 2 ≤
      kappa (meanLowerRoot 12452 θ ^ 2 / gPlus 12452) - 2 / (12452 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12452 *
      (kappa (meanLowerRoot 12452 θ ^ 2 / gPlus 12452) - 2 / (12452 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12452 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12452)
    linarith
  have ht : √(12 * gPlus 12452) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12452 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12452 12452 (11 / 1000) / √12452 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12452)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12452 (gMinus 12452) (gPlus 12452)
      (finiteEnergy 12452 12452 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12452) (hτ : 0 < (paperDesignP 12452).tau0 c) :
    eR c = (2 / (mA 12452 : ℝ)) *
      normSq (BstLean.Part150.bT 12452 12452 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12452).tau0 c)) /
      (2 / (12452 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12452).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12452).tau0 c))⁻¹ •
      BstLean.Part150.bT 12452 12452 (A1 c) (A2 c) c.1.2 ((paperDesignP 12452).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12452 : ℝ)) * normSq (bR c) / (2 / (12452 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12452}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12452) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12452).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12452 : ℝ) * (paperDesignP 12452).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12452 12452 c.1.2 ((paperDesignP 12452).tau0 c) :=
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

end BstLean.Part266.Row12452

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12453 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12453).real (BstLean.Part211.CentreSource 12453 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12453) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12453 160 (6 / 1000)
  have hj := jS_160_le (n := 12453) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12453 160 (6 / 1000) ^ 2 * 12453 /
      (((12453 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12453 160 (6 / 1000) ^ 2 * 12453 /
      (((12453 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12453 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12453 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12453) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12453 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12453

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12453) :=
  Ethm (paperCentres 12453) ∩ Ethp (paperCentres 12453)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12453)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12453)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12453) (paperCentres 12453)
  have he : exp (-(45 / 10000 * (12453 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12453 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12453) :=
  (passEvent ∩ agentEv (paperDesignP 12453) (DirectionError 12453) ∩
    agentEv (paperDesignP 12453) (CentreSources 12453 12453)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12453)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12453) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12453) hτ
  have hC := centreSources_ret_charge_row 12453 (paperDesignP 12453) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12453)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12453) (CentreSources 12453 12453)
  direction : analyticBase ⊆ agentEv (paperDesignP 12453) (DirectionError 12453)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12453)) : Set (Ret 12453) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12453)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12453)}
    (hT : (retDist (paperCentres 12453)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12453)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12453)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12453)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12453)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12453)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12453

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12453 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12453 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12453 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12453 12453 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12453)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12453)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12453
  have hb0 := BstLean.Part150.betaJ_nonneg 12453
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12453 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12453 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12453 * BstLean.Part150.betaJ 12453) * 12453) ≤
      (31736607 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12453)) * 12453 := by gcongr <;> linarith
      _ ≤ ((31736607 / 200000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12453 * 12453 *
      (1 + BstLean.Part154.deltaChi 12453 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181631971 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12453 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181631971 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12453 : ℝ) / BstLean.Part154.csC) ≤ (49027179 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12453 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((49027179 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12453 : ℝ) * (31736607 / 200000) +
        2 * (1792 / 10000 / 12453) * (181631971 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (49027179 / 500000) *
          (81 / 1000 / 12453 + (1792 / 10000 / 12453) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12453

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12453
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12453 ∧
    1 ≤ gPlus 12453 ∧ gPlus 12453 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12453 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12453 : ℝ) < √(1 - 2 / (12453 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12453 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12453 (gMinus 12453) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12453 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12453 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12453 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12453)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12453 (gMinus 12453) (gPlus 12453)
      (finiteEnergy 12453 12453 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12453 (gMinus 12453) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12453 (gMinus 12453) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12453 (gMinus 12453) (54 / 100))
    (by linarith : energyRatio 12453 (gMinus 12453) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12453 (gMinus 12453) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12453 * kappa (energyRatio 12453 (gMinus 12453) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12453) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12453 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12453 12453 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12453 12453 (11 / 1000) / √12453 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12453)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12453 * kappa (energyRatio 12453 (gMinus 12453) (54 / 100))) +
      2 * √(12 * gPlus 12453) / 12453 + finiteEnergy 12453 12453 (11 / 1000) / √12453 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12453 θ ∧ meanLowerRoot 12453 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12453 - 2 / (12453 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12453 - 2 / (12453 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12453 θ ^ 2 / gPlus 12453) - 2 / (12453 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12453 * (kappa (meanLowerRoot 12453 θ ^ 2 / gPlus 12453) -
        2 / (12453 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12453) / 12453 -
        finiteEnergy 12453 12453 (11 / 1000) / √12453 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12453 θ ^ 2 / gPlus 12453 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12453)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12453 θ ^ 2 / gPlus 12453 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12453)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12453 θ ^ 2 / gPlus 12453 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12453 ^ 2 ≤
      kappa (meanLowerRoot 12453 θ ^ 2 / gPlus 12453) - 2 / (12453 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12453 *
      (kappa (meanLowerRoot 12453 θ ^ 2 / gPlus 12453) - 2 / (12453 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12453 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12453)
    linarith
  have ht : √(12 * gPlus 12453) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12453 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12453 12453 (11 / 1000) / √12453 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12453)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12453 (gMinus 12453) (gPlus 12453)
      (finiteEnergy 12453 12453 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12453) (hτ : 0 < (paperDesignP 12453).tau0 c) :
    eR c = (2 / (mA 12453 : ℝ)) *
      normSq (BstLean.Part150.bT 12453 12453 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12453).tau0 c)) /
      (2 / (12453 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12453).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12453).tau0 c))⁻¹ •
      BstLean.Part150.bT 12453 12453 (A1 c) (A2 c) c.1.2 ((paperDesignP 12453).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12453 : ℝ)) * normSq (bR c) / (2 / (12453 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12453}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12453) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12453).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12453 : ℝ) * (paperDesignP 12453).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12453 12453 c.1.2 ((paperDesignP 12453).tau0 c) :=
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

end BstLean.Part266.Row12453

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12454 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12454).real (BstLean.Part211.CentreSource 12454 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12454) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12454 160 (6 / 1000)
  have hj := jS_160_le (n := 12454) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12454 160 (6 / 1000) ^ 2 * 12454 /
      (((12454 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12454 160 (6 / 1000) ^ 2 * 12454 /
      (((12454 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12454 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12454 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12454) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12454 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12454

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12454) :=
  Ethm (paperCentres 12454) ∩ Ethp (paperCentres 12454)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12454)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12454)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12454) (paperCentres 12454)
  have he : exp (-(45 / 10000 * (12454 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12454 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12454) :=
  (passEvent ∩ agentEv (paperDesignP 12454) (DirectionError 12454) ∩
    agentEv (paperDesignP 12454) (CentreSources 12454 12454)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12454)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12454) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12454) hτ
  have hC := centreSources_ret_charge_row 12454 (paperDesignP 12454) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12454)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12454) (CentreSources 12454 12454)
  direction : analyticBase ⊆ agentEv (paperDesignP 12454) (DirectionError 12454)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12454)) : Set (Ret 12454) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12454)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12454)}
    (hT : (retDist (paperCentres 12454)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12454)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12454)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12454)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12454)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12454)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12454

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12454 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12454 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12454 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12454 12454 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12454)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12454)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12454
  have hb0 := BstLean.Part150.betaJ_nonneg 12454
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12454 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12454 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12454 * BstLean.Part150.betaJ 12454) * 12454) ≤
      (79344703 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12454)) * 12454 := by gcongr <;> linarith
      _ ≤ ((79344703 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12454 * 12454 *
      (1 + BstLean.Part154.deltaChi 12454 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181639263 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12454 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181639263 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12454 : ℝ) / BstLean.Part154.csC) ≤ (19611659 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12454 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19611659 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12454 : ℝ) * (79344703 / 500000) +
        2 * (1792 / 10000 / 12454) * (181639263 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (19611659 / 200000) *
          (81 / 1000 / 12454 + (1792 / 10000 / 12454) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12454

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12454
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12454 ∧
    1 ≤ gPlus 12454 ∧ gPlus 12454 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12454 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12454 : ℝ) < √(1 - 2 / (12454 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12454 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12454 (gMinus 12454) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12454 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12454 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12454 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12454)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12454 (gMinus 12454) (gPlus 12454)
      (finiteEnergy 12454 12454 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12454 (gMinus 12454) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12454 (gMinus 12454) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12454 (gMinus 12454) (54 / 100))
    (by linarith : energyRatio 12454 (gMinus 12454) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12454 (gMinus 12454) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12454 * kappa (energyRatio 12454 (gMinus 12454) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12454) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12454 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12454 12454 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12454 12454 (11 / 1000) / √12454 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12454)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12454 * kappa (energyRatio 12454 (gMinus 12454) (54 / 100))) +
      2 * √(12 * gPlus 12454) / 12454 + finiteEnergy 12454 12454 (11 / 1000) / √12454 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12454 θ ∧ meanLowerRoot 12454 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12454 - 2 / (12454 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12454 - 2 / (12454 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12454 θ ^ 2 / gPlus 12454) - 2 / (12454 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12454 * (kappa (meanLowerRoot 12454 θ ^ 2 / gPlus 12454) -
        2 / (12454 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12454) / 12454 -
        finiteEnergy 12454 12454 (11 / 1000) / √12454 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12454 θ ^ 2 / gPlus 12454 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12454)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12454 θ ^ 2 / gPlus 12454 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12454)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12454 θ ^ 2 / gPlus 12454 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12454 ^ 2 ≤
      kappa (meanLowerRoot 12454 θ ^ 2 / gPlus 12454) - 2 / (12454 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12454 *
      (kappa (meanLowerRoot 12454 θ ^ 2 / gPlus 12454) - 2 / (12454 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12454 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12454)
    linarith
  have ht : √(12 * gPlus 12454) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12454 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12454 12454 (11 / 1000) / √12454 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12454)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12454 (gMinus 12454) (gPlus 12454)
      (finiteEnergy 12454 12454 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12454) (hτ : 0 < (paperDesignP 12454).tau0 c) :
    eR c = (2 / (mA 12454 : ℝ)) *
      normSq (BstLean.Part150.bT 12454 12454 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12454).tau0 c)) /
      (2 / (12454 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12454).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12454).tau0 c))⁻¹ •
      BstLean.Part150.bT 12454 12454 (A1 c) (A2 c) c.1.2 ((paperDesignP 12454).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12454 : ℝ)) * normSq (bR c) / (2 / (12454 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12454}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12454) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12454).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12454 : ℝ) * (paperDesignP 12454).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12454 12454 c.1.2 ((paperDesignP 12454).tau0 c) :=
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

end BstLean.Part266.Row12454

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12455 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12455).real (BstLean.Part211.CentreSource 12455 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12455) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12455 160 (6 / 1000)
  have hj := jS_160_le (n := 12455) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12455 160 (6 / 1000) ^ 2 * 12455 /
      (((12455 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12455 160 (6 / 1000) ^ 2 * 12455 /
      (((12455 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12455 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12455 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12455) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12455 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12455

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12455) :=
  Ethm (paperCentres 12455) ∩ Ethp (paperCentres 12455)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12455)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12455)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12455) (paperCentres 12455)
  have he : exp (-(45 / 10000 * (12455 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12455 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12455) :=
  (passEvent ∩ agentEv (paperDesignP 12455) (DirectionError 12455) ∩
    agentEv (paperDesignP 12455) (CentreSources 12455 12455)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12455)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12455) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12455) hτ
  have hC := centreSources_ret_charge_row 12455 (paperDesignP 12455) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12455)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12455) (CentreSources 12455 12455)
  direction : analyticBase ⊆ agentEv (paperDesignP 12455) (DirectionError 12455)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12455)) : Set (Ret 12455) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12455)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12455)}
    (hT : (retDist (paperCentres 12455)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12455)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12455)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12455)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12455)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12455)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12455

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12455 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12455 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12455 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12455 12455 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12455)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12455)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12455
  have hb0 := BstLean.Part150.betaJ_nonneg 12455
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12455 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12455 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12455 * BstLean.Part150.betaJ 12455) * 12455) ≤
      (158695777 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12455)) * 12455 := by gcongr <;> linarith
      _ ≤ ((158695777 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12455 * 12455 *
      (1 + BstLean.Part154.deltaChi 12455 12 + 2 / π) / BstLean.Part154.csC) ≤
      (45411639 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12455 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((45411639 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12455 : ℝ) / BstLean.Part154.csC) ≤ (12257779 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12455 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((12257779 / 125000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12455 : ℝ) * (158695777 / 1000000) +
        2 * (1792 / 10000 / 12455) * (45411639 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (12257779 / 125000) *
          (81 / 1000 / 12455 + (1792 / 10000 / 12455) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12455

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12455
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12455 ∧
    1 ≤ gPlus 12455 ∧ gPlus 12455 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12455 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12455 : ℝ) < √(1 - 2 / (12455 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12455 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12455 (gMinus 12455) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12455 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12455 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12455 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12455)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12455 (gMinus 12455) (gPlus 12455)
      (finiteEnergy 12455 12455 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12455 (gMinus 12455) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12455 (gMinus 12455) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12455 (gMinus 12455) (54 / 100))
    (by linarith : energyRatio 12455 (gMinus 12455) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12455 (gMinus 12455) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12455 * kappa (energyRatio 12455 (gMinus 12455) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12455) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12455 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12455 12455 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12455 12455 (11 / 1000) / √12455 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12455)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12455 * kappa (energyRatio 12455 (gMinus 12455) (54 / 100))) +
      2 * √(12 * gPlus 12455) / 12455 + finiteEnergy 12455 12455 (11 / 1000) / √12455 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12455 θ ∧ meanLowerRoot 12455 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12455 - 2 / (12455 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12455 - 2 / (12455 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12455 θ ^ 2 / gPlus 12455) - 2 / (12455 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12455 * (kappa (meanLowerRoot 12455 θ ^ 2 / gPlus 12455) -
        2 / (12455 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12455) / 12455 -
        finiteEnergy 12455 12455 (11 / 1000) / √12455 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12455 θ ^ 2 / gPlus 12455 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12455)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12455 θ ^ 2 / gPlus 12455 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12455)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12455 θ ^ 2 / gPlus 12455 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12455 ^ 2 ≤
      kappa (meanLowerRoot 12455 θ ^ 2 / gPlus 12455) - 2 / (12455 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12455 *
      (kappa (meanLowerRoot 12455 θ ^ 2 / gPlus 12455) - 2 / (12455 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12455 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12455)
    linarith
  have ht : √(12 * gPlus 12455) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12455 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12455 12455 (11 / 1000) / √12455 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12455)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12455 (gMinus 12455) (gPlus 12455)
      (finiteEnergy 12455 12455 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12455) (hτ : 0 < (paperDesignP 12455).tau0 c) :
    eR c = (2 / (mA 12455 : ℝ)) *
      normSq (BstLean.Part150.bT 12455 12455 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12455).tau0 c)) /
      (2 / (12455 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12455).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12455).tau0 c))⁻¹ •
      BstLean.Part150.bT 12455 12455 (A1 c) (A2 c) c.1.2 ((paperDesignP 12455).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12455 : ℝ)) * normSq (bR c) / (2 / (12455 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12455}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12455) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12455).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12455 : ℝ) * (paperDesignP 12455).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12455 12455 c.1.2 ((paperDesignP 12455).tau0 c) :=
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

end BstLean.Part266.Row12455

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12456 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12456).real (BstLean.Part211.CentreSource 12456 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12456) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12456 160 (6 / 1000)
  have hj := jS_160_le (n := 12456) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12456 160 (6 / 1000) ^ 2 * 12456 /
      (((12456 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12456 160 (6 / 1000) ^ 2 * 12456 /
      (((12456 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12456 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12456 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12456) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12456 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12456

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12456) :=
  Ethm (paperCentres 12456) ∩ Ethp (paperCentres 12456)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12456)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12456)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12456) (paperCentres 12456)
  have he : exp (-(45 / 10000 * (12456 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12456 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12456) :=
  (passEvent ∩ agentEv (paperDesignP 12456) (DirectionError 12456) ∩
    agentEv (paperDesignP 12456) (CentreSources 12456 12456)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12456)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12456) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12456) hτ
  have hC := centreSources_ret_charge_row 12456 (paperDesignP 12456) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12456)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12456) (CentreSources 12456 12456)
  direction : analyticBase ⊆ agentEv (paperDesignP 12456) (DirectionError 12456)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12456)) : Set (Ret 12456) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12456)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12456)}
    (hT : (retDist (paperCentres 12456)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12456)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12456)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12456)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12456)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12456)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12456

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12456 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12456 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12456 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12456 12456 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12456)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12456)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12456
  have hb0 := BstLean.Part150.betaJ_nonneg 12456
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12456 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12456 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12456 * BstLean.Part150.betaJ 12456) * 12456) ≤
      (39675537 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12456)) * 12456 := by gcongr <;> linarith
      _ ≤ ((39675537 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12456 * 12456 *
      (1 + BstLean.Part154.deltaChi 12456 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181653847 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12456 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181653847 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12456 : ℝ) / BstLean.Part154.csC) ≤ (98066169 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12456 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98066169 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12456 : ℝ) * (39675537 / 250000) +
        2 * (1792 / 10000 / 12456) * (181653847 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (98066169 / 1000000) *
          (81 / 1000 / 12456 + (1792 / 10000 / 12456) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12456

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12456
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12456 ∧
    1 ≤ gPlus 12456 ∧ gPlus 12456 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12456 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12456 : ℝ) < √(1 - 2 / (12456 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12456 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12456 (gMinus 12456) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12456 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12456 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12456 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12456)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12456 (gMinus 12456) (gPlus 12456)
      (finiteEnergy 12456 12456 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12456 (gMinus 12456) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12456 (gMinus 12456) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12456 (gMinus 12456) (54 / 100))
    (by linarith : energyRatio 12456 (gMinus 12456) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12456 (gMinus 12456) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12456 * kappa (energyRatio 12456 (gMinus 12456) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12456) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12456 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12456 12456 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12456 12456 (11 / 1000) / √12456 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12456)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12456 * kappa (energyRatio 12456 (gMinus 12456) (54 / 100))) +
      2 * √(12 * gPlus 12456) / 12456 + finiteEnergy 12456 12456 (11 / 1000) / √12456 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12456 θ ∧ meanLowerRoot 12456 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12456 - 2 / (12456 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12456 - 2 / (12456 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12456 θ ^ 2 / gPlus 12456) - 2 / (12456 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12456 * (kappa (meanLowerRoot 12456 θ ^ 2 / gPlus 12456) -
        2 / (12456 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12456) / 12456 -
        finiteEnergy 12456 12456 (11 / 1000) / √12456 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12456 θ ^ 2 / gPlus 12456 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12456)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12456 θ ^ 2 / gPlus 12456 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12456)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12456 θ ^ 2 / gPlus 12456 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12456 ^ 2 ≤
      kappa (meanLowerRoot 12456 θ ^ 2 / gPlus 12456) - 2 / (12456 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12456 *
      (kappa (meanLowerRoot 12456 θ ^ 2 / gPlus 12456) - 2 / (12456 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12456 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12456)
    linarith
  have ht : √(12 * gPlus 12456) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12456 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12456 12456 (11 / 1000) / √12456 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12456)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12456 (gMinus 12456) (gPlus 12456)
      (finiteEnergy 12456 12456 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12456) (hτ : 0 < (paperDesignP 12456).tau0 c) :
    eR c = (2 / (mA 12456 : ℝ)) *
      normSq (BstLean.Part150.bT 12456 12456 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12456).tau0 c)) /
      (2 / (12456 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12456).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12456).tau0 c))⁻¹ •
      BstLean.Part150.bT 12456 12456 (A1 c) (A2 c) c.1.2 ((paperDesignP 12456).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12456 : ℝ)) * normSq (bR c) / (2 / (12456 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12456}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12456) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12456).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12456 : ℝ) * (paperDesignP 12456).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12456 12456 c.1.2 ((paperDesignP 12456).tau0 c) :=
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

end BstLean.Part266.Row12456

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12457 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12457).real (BstLean.Part211.CentreSource 12457 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12457) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12457 160 (6 / 1000)
  have hj := jS_160_le (n := 12457) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12457 160 (6 / 1000) ^ 2 * 12457 /
      (((12457 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12457 160 (6 / 1000) ^ 2 * 12457 /
      (((12457 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12457 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12457 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12457) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12457 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12457

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12457) :=
  Ethm (paperCentres 12457) ∩ Ethp (paperCentres 12457)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12457)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12457)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12457) (paperCentres 12457)
  have he : exp (-(45 / 10000 * (12457 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12457 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12457) :=
  (passEvent ∩ agentEv (paperDesignP 12457) (DirectionError 12457) ∩
    agentEv (paperDesignP 12457) (CentreSources 12457 12457)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12457)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12457) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12457) hτ
  have hC := centreSources_ret_charge_row 12457 (paperDesignP 12457) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12457)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12457) (CentreSources 12457 12457)
  direction : analyticBase ⊆ agentEv (paperDesignP 12457) (DirectionError 12457)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12457)) : Set (Ret 12457) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12457)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12457)}
    (hT : (retDist (paperCentres 12457)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12457)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12457)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12457)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12457)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12457)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12457

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12457 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12457 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12457 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12457 12457 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12457)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12457)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12457
  have hb0 := BstLean.Part150.betaJ_nonneg 12457
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12457 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12457 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12457 * BstLean.Part150.betaJ 12457) * 12457) ≤
      (79354259 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12457)) * 12457 := by gcongr <;> linarith
      _ ≤ ((79354259 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12457 * 12457 *
      (1 + BstLean.Part154.deltaChi 12457 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181661139 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12457 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181661139 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12457 : ℝ) / BstLean.Part154.csC) ≤ (19614021 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12457 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19614021 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12457 : ℝ) * (79354259 / 500000) +
        2 * (1792 / 10000 / 12457) * (181661139 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (19614021 / 200000) *
          (81 / 1000 / 12457 + (1792 / 10000 / 12457) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12457

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12457
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12457 ∧
    1 ≤ gPlus 12457 ∧ gPlus 12457 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12457 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12457 : ℝ) < √(1 - 2 / (12457 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12457 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12457 (gMinus 12457) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12457 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12457 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12457 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12457)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12457 (gMinus 12457) (gPlus 12457)
      (finiteEnergy 12457 12457 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12457 (gMinus 12457) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12457 (gMinus 12457) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12457 (gMinus 12457) (54 / 100))
    (by linarith : energyRatio 12457 (gMinus 12457) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12457 (gMinus 12457) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12457 * kappa (energyRatio 12457 (gMinus 12457) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12457) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12457 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12457 12457 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12457 12457 (11 / 1000) / √12457 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12457)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12457 * kappa (energyRatio 12457 (gMinus 12457) (54 / 100))) +
      2 * √(12 * gPlus 12457) / 12457 + finiteEnergy 12457 12457 (11 / 1000) / √12457 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12457 θ ∧ meanLowerRoot 12457 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12457 - 2 / (12457 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12457 - 2 / (12457 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12457 θ ^ 2 / gPlus 12457) - 2 / (12457 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12457 * (kappa (meanLowerRoot 12457 θ ^ 2 / gPlus 12457) -
        2 / (12457 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12457) / 12457 -
        finiteEnergy 12457 12457 (11 / 1000) / √12457 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12457 θ ^ 2 / gPlus 12457 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12457)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12457 θ ^ 2 / gPlus 12457 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12457)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12457 θ ^ 2 / gPlus 12457 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12457 ^ 2 ≤
      kappa (meanLowerRoot 12457 θ ^ 2 / gPlus 12457) - 2 / (12457 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12457 *
      (kappa (meanLowerRoot 12457 θ ^ 2 / gPlus 12457) - 2 / (12457 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12457 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12457)
    linarith
  have ht : √(12 * gPlus 12457) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12457 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12457 12457 (11 / 1000) / √12457 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12457)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12457 (gMinus 12457) (gPlus 12457)
      (finiteEnergy 12457 12457 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12457) (hτ : 0 < (paperDesignP 12457).tau0 c) :
    eR c = (2 / (mA 12457 : ℝ)) *
      normSq (BstLean.Part150.bT 12457 12457 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12457).tau0 c)) /
      (2 / (12457 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12457).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12457).tau0 c))⁻¹ •
      BstLean.Part150.bT 12457 12457 (A1 c) (A2 c) c.1.2 ((paperDesignP 12457).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12457 : ℝ)) * normSq (bR c) / (2 / (12457 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12457}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12457) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12457).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12457 : ℝ) * (paperDesignP 12457).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12457 12457 c.1.2 ((paperDesignP 12457).tau0 c) :=
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

end BstLean.Part266.Row12457

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12458 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12458).real (BstLean.Part211.CentreSource 12458 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12458) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12458 160 (6 / 1000)
  have hj := jS_160_le (n := 12458) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12458 160 (6 / 1000) ^ 2 * 12458 /
      (((12458 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12458 160 (6 / 1000) ^ 2 * 12458 /
      (((12458 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12458 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12458 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12458) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12458 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12458

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12458) :=
  Ethm (paperCentres 12458) ∩ Ethp (paperCentres 12458)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12458)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12458)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12458) (paperCentres 12458)
  have he : exp (-(45 / 10000 * (12458 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12458 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12458) :=
  (passEvent ∩ agentEv (paperDesignP 12458) (DirectionError 12458) ∩
    agentEv (paperDesignP 12458) (CentreSources 12458 12458)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12458)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12458) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12458) hτ
  have hC := centreSources_ret_charge_row 12458 (paperDesignP 12458) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12458)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12458) (CentreSources 12458 12458)
  direction : analyticBase ⊆ agentEv (paperDesignP 12458) (DirectionError 12458)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12458)) : Set (Ret 12458) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12458)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12458)}
    (hT : (retDist (paperCentres 12458)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12458)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12458)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12458)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12458)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12458)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12458

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12458 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12458 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12458 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12458 12458 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12458)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12458)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12458
  have hb0 := BstLean.Part150.betaJ_nonneg 12458
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12458 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12458 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12458 * BstLean.Part150.betaJ 12458) * 12458) ≤
      (19839361 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12458)) * 12458 := by gcongr <;> linarith
      _ ≤ ((19839361 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12458 * 12458 *
      (1 + BstLean.Part154.deltaChi 12458 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181668431 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12458 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181668431 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12458 : ℝ) / BstLean.Part154.csC) ≤ (98074041 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12458 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98074041 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12458 : ℝ) * (19839361 / 125000) +
        2 * (1792 / 10000 / 12458) * (181668431 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (98074041 / 1000000) *
          (81 / 1000 / 12458 + (1792 / 10000 / 12458) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12458

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12458
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12458 ∧
    1 ≤ gPlus 12458 ∧ gPlus 12458 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12458 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12458 : ℝ) < √(1 - 2 / (12458 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12458 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12458 (gMinus 12458) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12458 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12458 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12458 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12458)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12458 (gMinus 12458) (gPlus 12458)
      (finiteEnergy 12458 12458 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12458 (gMinus 12458) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12458 (gMinus 12458) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12458 (gMinus 12458) (54 / 100))
    (by linarith : energyRatio 12458 (gMinus 12458) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12458 (gMinus 12458) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12458 * kappa (energyRatio 12458 (gMinus 12458) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12458) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12458 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12458 12458 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12458 12458 (11 / 1000) / √12458 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12458)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12458 * kappa (energyRatio 12458 (gMinus 12458) (54 / 100))) +
      2 * √(12 * gPlus 12458) / 12458 + finiteEnergy 12458 12458 (11 / 1000) / √12458 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12458 θ ∧ meanLowerRoot 12458 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12458 - 2 / (12458 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12458 - 2 / (12458 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12458 θ ^ 2 / gPlus 12458) - 2 / (12458 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12458 * (kappa (meanLowerRoot 12458 θ ^ 2 / gPlus 12458) -
        2 / (12458 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12458) / 12458 -
        finiteEnergy 12458 12458 (11 / 1000) / √12458 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12458 θ ^ 2 / gPlus 12458 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12458)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12458 θ ^ 2 / gPlus 12458 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12458)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12458 θ ^ 2 / gPlus 12458 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12458 ^ 2 ≤
      kappa (meanLowerRoot 12458 θ ^ 2 / gPlus 12458) - 2 / (12458 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12458 *
      (kappa (meanLowerRoot 12458 θ ^ 2 / gPlus 12458) - 2 / (12458 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12458 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12458)
    linarith
  have ht : √(12 * gPlus 12458) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12458 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12458 12458 (11 / 1000) / √12458 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12458)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12458 (gMinus 12458) (gPlus 12458)
      (finiteEnergy 12458 12458 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12458) (hτ : 0 < (paperDesignP 12458).tau0 c) :
    eR c = (2 / (mA 12458 : ℝ)) *
      normSq (BstLean.Part150.bT 12458 12458 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12458).tau0 c)) /
      (2 / (12458 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12458).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12458).tau0 c))⁻¹ •
      BstLean.Part150.bT 12458 12458 (A1 c) (A2 c) c.1.2 ((paperDesignP 12458).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12458 : ℝ)) * normSq (bR c) / (2 / (12458 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12458}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12458) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12458).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12458 : ℝ) * (paperDesignP 12458).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12458 12458 c.1.2 ((paperDesignP 12458).tau0 c) :=
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

end BstLean.Part266.Row12458

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12459 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12459).real (BstLean.Part211.CentreSource 12459 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12459) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12459 160 (6 / 1000)
  have hj := jS_160_le (n := 12459) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12459 160 (6 / 1000) ^ 2 * 12459 /
      (((12459 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12459 160 (6 / 1000) ^ 2 * 12459 /
      (((12459 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12459 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12459 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12459) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12459 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12459

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12459) :=
  Ethm (paperCentres 12459) ∩ Ethp (paperCentres 12459)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12459)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12459)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12459) (paperCentres 12459)
  have he : exp (-(45 / 10000 * (12459 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12459 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12459) :=
  (passEvent ∩ agentEv (paperDesignP 12459) (DirectionError 12459) ∩
    agentEv (paperDesignP 12459) (CentreSources 12459 12459)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12459)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12459) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12459) hτ
  have hC := centreSources_ret_charge_row 12459 (paperDesignP 12459) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12459)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12459) (CentreSources 12459 12459)
  direction : analyticBase ⊆ agentEv (paperDesignP 12459) (DirectionError 12459)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12459)) : Set (Ret 12459) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12459)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12459)}
    (hT : (retDist (paperCentres 12459)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12459)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12459)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12459)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12459)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12459)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12459

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12459 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12459 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12459 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12459 12459 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12459)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12459)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12459
  have hb0 := BstLean.Part150.betaJ_nonneg 12459
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12459 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12459 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12459 * BstLean.Part150.betaJ 12459) * 12459) ≤
      (79360629 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12459)) * 12459 := by gcongr <;> linarith
      _ ≤ ((79360629 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12459 * 12459 *
      (1 + BstLean.Part154.deltaChi 12459 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90837861 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12459 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90837861 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12459 : ℝ) / BstLean.Part154.csC) ≤ (98077977 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12459 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98077977 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12459 : ℝ) * (79360629 / 500000) +
        2 * (1792 / 10000 / 12459) * (90837861 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (98077977 / 1000000) *
          (81 / 1000 / 12459 + (1792 / 10000 / 12459) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12459

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12459
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12459 ∧
    1 ≤ gPlus 12459 ∧ gPlus 12459 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12459 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12459 : ℝ) < √(1 - 2 / (12459 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12459 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12459 (gMinus 12459) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12459 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12459 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12459 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12459)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12459 (gMinus 12459) (gPlus 12459)
      (finiteEnergy 12459 12459 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12459 (gMinus 12459) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12459 (gMinus 12459) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12459 (gMinus 12459) (54 / 100))
    (by linarith : energyRatio 12459 (gMinus 12459) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12459 (gMinus 12459) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12459 * kappa (energyRatio 12459 (gMinus 12459) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12459) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12459 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12459 12459 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12459 12459 (11 / 1000) / √12459 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12459)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12459 * kappa (energyRatio 12459 (gMinus 12459) (54 / 100))) +
      2 * √(12 * gPlus 12459) / 12459 + finiteEnergy 12459 12459 (11 / 1000) / √12459 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12459 θ ∧ meanLowerRoot 12459 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12459 - 2 / (12459 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12459 - 2 / (12459 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12459 θ ^ 2 / gPlus 12459) - 2 / (12459 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12459 * (kappa (meanLowerRoot 12459 θ ^ 2 / gPlus 12459) -
        2 / (12459 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12459) / 12459 -
        finiteEnergy 12459 12459 (11 / 1000) / √12459 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12459 θ ^ 2 / gPlus 12459 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12459)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12459 θ ^ 2 / gPlus 12459 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12459)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12459 θ ^ 2 / gPlus 12459 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12459 ^ 2 ≤
      kappa (meanLowerRoot 12459 θ ^ 2 / gPlus 12459) - 2 / (12459 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12459 *
      (kappa (meanLowerRoot 12459 θ ^ 2 / gPlus 12459) - 2 / (12459 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12459 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12459)
    linarith
  have ht : √(12 * gPlus 12459) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12459 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12459 12459 (11 / 1000) / √12459 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12459)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12459 (gMinus 12459) (gPlus 12459)
      (finiteEnergy 12459 12459 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12459) (hτ : 0 < (paperDesignP 12459).tau0 c) :
    eR c = (2 / (mA 12459 : ℝ)) *
      normSq (BstLean.Part150.bT 12459 12459 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12459).tau0 c)) /
      (2 / (12459 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12459).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12459).tau0 c))⁻¹ •
      BstLean.Part150.bT 12459 12459 (A1 c) (A2 c) c.1.2 ((paperDesignP 12459).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12459 : ℝ)) * normSq (bR c) / (2 / (12459 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12459}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12459) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12459).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12459 : ℝ) * (paperDesignP 12459).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12459 12459 c.1.2 ((paperDesignP 12459).tau0 c) :=
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

end BstLean.Part266.Row12459

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12460 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12460).real (BstLean.Part211.CentreSource 12460 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12460) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12460 160 (6 / 1000)
  have hj := jS_160_le (n := 12460) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12460 160 (6 / 1000) ^ 2 * 12460 /
      (((12460 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12460 160 (6 / 1000) ^ 2 * 12460 /
      (((12460 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12460 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12460 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12460) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12460 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12460

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12460) :=
  Ethm (paperCentres 12460) ∩ Ethp (paperCentres 12460)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12460)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12460)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12460) (paperCentres 12460)
  have he : exp (-(45 / 10000 * (12460 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12460 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12460) :=
  (passEvent ∩ agentEv (paperDesignP 12460) (DirectionError 12460) ∩
    agentEv (paperDesignP 12460) (CentreSources 12460 12460)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12460)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12460) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12460) hτ
  have hC := centreSources_ret_charge_row 12460 (paperDesignP 12460) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12460)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12460) (CentreSources 12460 12460)
  direction : analyticBase ⊆ agentEv (paperDesignP 12460) (DirectionError 12460)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12460)) : Set (Ret 12460) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12460)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12460)}
    (hT : (retDist (paperCentres 12460)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12460)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12460)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12460)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12460)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12460)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12460

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12460 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12460 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12460 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12460 12460 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12460)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12460)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12460
  have hb0 := BstLean.Part150.betaJ_nonneg 12460
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12460 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12460 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12460 * BstLean.Part150.betaJ 12460) * 12460) ≤
      (158727627 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12460)) * 12460 := by gcongr <;> linarith
      _ ≤ ((158727627 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12460 * 12460 *
      (1 + BstLean.Part154.deltaChi 12460 12 + 2 / π) / BstLean.Part154.csC) ≤
      (45420753 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12460 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((45420753 / 250000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12460 : ℝ) / BstLean.Part154.csC) ≤ (98081913 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12460 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98081913 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12460 : ℝ) * (158727627 / 1000000) +
        2 * (1792 / 10000 / 12460) * (45420753 / 250000) +
        4 * (1 / 2.506628) * 1.036505 * (98081913 / 1000000) *
          (81 / 1000 / 12460 + (1792 / 10000 / 12460) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12460

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12460
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12460 ∧
    1 ≤ gPlus 12460 ∧ gPlus 12460 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12460 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12460 : ℝ) < √(1 - 2 / (12460 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12460 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12460 (gMinus 12460) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12460 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12460 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12460 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12460)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12460 (gMinus 12460) (gPlus 12460)
      (finiteEnergy 12460 12460 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12460 (gMinus 12460) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12460 (gMinus 12460) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12460 (gMinus 12460) (54 / 100))
    (by linarith : energyRatio 12460 (gMinus 12460) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12460 (gMinus 12460) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12460 * kappa (energyRatio 12460 (gMinus 12460) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12460) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12460 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12460 12460 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12460 12460 (11 / 1000) / √12460 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12460)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12460 * kappa (energyRatio 12460 (gMinus 12460) (54 / 100))) +
      2 * √(12 * gPlus 12460) / 12460 + finiteEnergy 12460 12460 (11 / 1000) / √12460 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12460 θ ∧ meanLowerRoot 12460 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12460 - 2 / (12460 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12460 - 2 / (12460 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12460 θ ^ 2 / gPlus 12460) - 2 / (12460 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12460 * (kappa (meanLowerRoot 12460 θ ^ 2 / gPlus 12460) -
        2 / (12460 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12460) / 12460 -
        finiteEnergy 12460 12460 (11 / 1000) / √12460 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12460 θ ^ 2 / gPlus 12460 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12460)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12460 θ ^ 2 / gPlus 12460 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12460)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12460 θ ^ 2 / gPlus 12460 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12460 ^ 2 ≤
      kappa (meanLowerRoot 12460 θ ^ 2 / gPlus 12460) - 2 / (12460 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12460 *
      (kappa (meanLowerRoot 12460 θ ^ 2 / gPlus 12460) - 2 / (12460 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12460 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12460)
    linarith
  have ht : √(12 * gPlus 12460) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12460 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12460 12460 (11 / 1000) / √12460 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12460)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12460 (gMinus 12460) (gPlus 12460)
      (finiteEnergy 12460 12460 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12460) (hτ : 0 < (paperDesignP 12460).tau0 c) :
    eR c = (2 / (mA 12460 : ℝ)) *
      normSq (BstLean.Part150.bT 12460 12460 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12460).tau0 c)) /
      (2 / (12460 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12460).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12460).tau0 c))⁻¹ •
      BstLean.Part150.bT 12460 12460 (A1 c) (A2 c) c.1.2 ((paperDesignP 12460).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12460 : ℝ)) * normSq (bR c) / (2 / (12460 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12460}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12460) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12460).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12460 : ℝ) * (paperDesignP 12460).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12460 12460 c.1.2 ((paperDesignP 12460).tau0 c) :=
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

end BstLean.Part266.Row12460

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12461 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12461).real (BstLean.Part211.CentreSource 12461 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12461) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12461 160 (6 / 1000)
  have hj := jS_160_le (n := 12461) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12461 160 (6 / 1000) ^ 2 * 12461 /
      (((12461 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12461 160 (6 / 1000) ^ 2 * 12461 /
      (((12461 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12461 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12461 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12461) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12461 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12461

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12461) :=
  Ethm (paperCentres 12461) ∩ Ethp (paperCentres 12461)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12461)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12461)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12461) (paperCentres 12461)
  have he : exp (-(45 / 10000 * (12461 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12461 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12461) :=
  (passEvent ∩ agentEv (paperDesignP 12461) (DirectionError 12461) ∩
    agentEv (paperDesignP 12461) (CentreSources 12461 12461)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12461)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12461) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12461) hτ
  have hC := centreSources_ret_charge_row 12461 (paperDesignP 12461) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12461)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12461) (CentreSources 12461 12461)
  direction : analyticBase ⊆ agentEv (paperDesignP 12461) (DirectionError 12461)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12461)) : Set (Ret 12461) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12461)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12461)}
    (hT : (retDist (paperCentres 12461)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12461)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12461)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12461)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12461)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12461)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12461

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12461 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12461 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12461 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12461 12461 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12461)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12461)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12461
  have hb0 := BstLean.Part150.betaJ_nonneg 12461
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12461 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12461 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12461 * BstLean.Part150.betaJ 12461) * 12461) ≤
      (158733997 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12461)) * 12461 := by gcongr <;> linarith
      _ ≤ ((158733997 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12461 * 12461 *
      (1 + BstLean.Part154.deltaChi 12461 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181690303 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12461 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181690303 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12461 : ℝ) / BstLean.Part154.csC) ≤ (98085849 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12461 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98085849 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12461 : ℝ) * (158733997 / 1000000) +
        2 * (1792 / 10000 / 12461) * (181690303 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (98085849 / 1000000) *
          (81 / 1000 / 12461 + (1792 / 10000 / 12461) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12461

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12461
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12461 ∧
    1 ≤ gPlus 12461 ∧ gPlus 12461 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12461 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12461 : ℝ) < √(1 - 2 / (12461 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12461 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12461 (gMinus 12461) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12461 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12461 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12461 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12461)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12461 (gMinus 12461) (gPlus 12461)
      (finiteEnergy 12461 12461 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12461 (gMinus 12461) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12461 (gMinus 12461) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12461 (gMinus 12461) (54 / 100))
    (by linarith : energyRatio 12461 (gMinus 12461) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12461 (gMinus 12461) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12461 * kappa (energyRatio 12461 (gMinus 12461) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12461) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12461 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12461 12461 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12461 12461 (11 / 1000) / √12461 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12461)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12461 * kappa (energyRatio 12461 (gMinus 12461) (54 / 100))) +
      2 * √(12 * gPlus 12461) / 12461 + finiteEnergy 12461 12461 (11 / 1000) / √12461 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12461 θ ∧ meanLowerRoot 12461 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12461 - 2 / (12461 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12461 - 2 / (12461 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12461 θ ^ 2 / gPlus 12461) - 2 / (12461 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12461 * (kappa (meanLowerRoot 12461 θ ^ 2 / gPlus 12461) -
        2 / (12461 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12461) / 12461 -
        finiteEnergy 12461 12461 (11 / 1000) / √12461 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12461 θ ^ 2 / gPlus 12461 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12461)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12461 θ ^ 2 / gPlus 12461 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12461)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12461 θ ^ 2 / gPlus 12461 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12461 ^ 2 ≤
      kappa (meanLowerRoot 12461 θ ^ 2 / gPlus 12461) - 2 / (12461 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12461 *
      (kappa (meanLowerRoot 12461 θ ^ 2 / gPlus 12461) - 2 / (12461 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12461 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12461)
    linarith
  have ht : √(12 * gPlus 12461) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12461 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12461 12461 (11 / 1000) / √12461 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12461)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12461 (gMinus 12461) (gPlus 12461)
      (finiteEnergy 12461 12461 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12461) (hτ : 0 < (paperDesignP 12461).tau0 c) :
    eR c = (2 / (mA 12461 : ℝ)) *
      normSq (BstLean.Part150.bT 12461 12461 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12461).tau0 c)) /
      (2 / (12461 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12461).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12461).tau0 c))⁻¹ •
      BstLean.Part150.bT 12461 12461 (A1 c) (A2 c) c.1.2 ((paperDesignP 12461).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12461 : ℝ)) * normSq (bR c) / (2 / (12461 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12461}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12461) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12461).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12461 : ℝ) * (paperDesignP 12461).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12461 12461 c.1.2 ((paperDesignP 12461).tau0 c) :=
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

end BstLean.Part266.Row12461

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12462 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12462).real (BstLean.Part211.CentreSource 12462 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12462) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12462 160 (6 / 1000)
  have hj := jS_160_le (n := 12462) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12462 160 (6 / 1000) ^ 2 * 12462 /
      (((12462 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12462 160 (6 / 1000) ^ 2 * 12462 /
      (((12462 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12462 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12462 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12462) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12462 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12462

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12462) :=
  Ethm (paperCentres 12462) ∩ Ethp (paperCentres 12462)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12462)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12462)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12462) (paperCentres 12462)
  have he : exp (-(45 / 10000 * (12462 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12462 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12462) :=
  (passEvent ∩ agentEv (paperDesignP 12462) (DirectionError 12462) ∩
    agentEv (paperDesignP 12462) (CentreSources 12462 12462)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12462)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12462) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12462) hτ
  have hC := centreSources_ret_charge_row 12462 (paperDesignP 12462) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12462)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12462) (CentreSources 12462 12462)
  direction : analyticBase ⊆ agentEv (paperDesignP 12462) (DirectionError 12462)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12462)) : Set (Ret 12462) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12462)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12462)}
    (hT : (retDist (paperCentres 12462)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12462)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12462)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12462)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12462)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12462)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12462

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12462 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12462 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12462 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12462 12462 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12462)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12462)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12462
  have hb0 := BstLean.Part150.betaJ_nonneg 12462
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12462 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12462 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12462 * BstLean.Part150.betaJ 12462) * 12462) ≤
      (79370183 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12462)) * 12462 := by gcongr <;> linarith
      _ ≤ ((79370183 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12462 * 12462 *
      (1 + BstLean.Part154.deltaChi 12462 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181697593 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12462 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181697593 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12462 : ℝ) / BstLean.Part154.csC) ≤ (19617957 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12462 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19617957 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12462 : ℝ) * (79370183 / 500000) +
        2 * (1792 / 10000 / 12462) * (181697593 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (19617957 / 200000) *
          (81 / 1000 / 12462 + (1792 / 10000 / 12462) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12462

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12462
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12462 ∧
    1 ≤ gPlus 12462 ∧ gPlus 12462 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12462 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12462 : ℝ) < √(1 - 2 / (12462 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12462 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12462 (gMinus 12462) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12462 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12462 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12462 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12462)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12462 (gMinus 12462) (gPlus 12462)
      (finiteEnergy 12462 12462 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12462 (gMinus 12462) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12462 (gMinus 12462) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12462 (gMinus 12462) (54 / 100))
    (by linarith : energyRatio 12462 (gMinus 12462) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12462 (gMinus 12462) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12462 * kappa (energyRatio 12462 (gMinus 12462) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12462) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12462 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12462 12462 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12462 12462 (11 / 1000) / √12462 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12462)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12462 * kappa (energyRatio 12462 (gMinus 12462) (54 / 100))) +
      2 * √(12 * gPlus 12462) / 12462 + finiteEnergy 12462 12462 (11 / 1000) / √12462 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12462 θ ∧ meanLowerRoot 12462 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12462 - 2 / (12462 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12462 - 2 / (12462 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12462 θ ^ 2 / gPlus 12462) - 2 / (12462 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12462 * (kappa (meanLowerRoot 12462 θ ^ 2 / gPlus 12462) -
        2 / (12462 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12462) / 12462 -
        finiteEnergy 12462 12462 (11 / 1000) / √12462 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12462 θ ^ 2 / gPlus 12462 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12462)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12462 θ ^ 2 / gPlus 12462 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12462)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12462 θ ^ 2 / gPlus 12462 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12462 ^ 2 ≤
      kappa (meanLowerRoot 12462 θ ^ 2 / gPlus 12462) - 2 / (12462 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12462 *
      (kappa (meanLowerRoot 12462 θ ^ 2 / gPlus 12462) - 2 / (12462 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12462 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12462)
    linarith
  have ht : √(12 * gPlus 12462) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12462 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12462 12462 (11 / 1000) / √12462 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12462)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12462 (gMinus 12462) (gPlus 12462)
      (finiteEnergy 12462 12462 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12462) (hτ : 0 < (paperDesignP 12462).tau0 c) :
    eR c = (2 / (mA 12462 : ℝ)) *
      normSq (BstLean.Part150.bT 12462 12462 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12462).tau0 c)) /
      (2 / (12462 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12462).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12462).tau0 c))⁻¹ •
      BstLean.Part150.bT 12462 12462 (A1 c) (A2 c) c.1.2 ((paperDesignP 12462).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12462 : ℝ)) * normSq (bR c) / (2 / (12462 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12462}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12462) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12462).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12462 : ℝ) * (paperDesignP 12462).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12462 12462 c.1.2 ((paperDesignP 12462).tau0 c) :=
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

end BstLean.Part266.Row12462

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12463 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12463).real (BstLean.Part211.CentreSource 12463 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12463) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12463 160 (6 / 1000)
  have hj := jS_160_le (n := 12463) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12463 160 (6 / 1000) ^ 2 * 12463 /
      (((12463 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12463 160 (6 / 1000) ^ 2 * 12463 /
      (((12463 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12463 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12463 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12463) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12463 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12463

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12463) :=
  Ethm (paperCentres 12463) ∩ Ethp (paperCentres 12463)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12463)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12463)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12463) (paperCentres 12463)
  have he : exp (-(45 / 10000 * (12463 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12463 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12463) :=
  (passEvent ∩ agentEv (paperDesignP 12463) (DirectionError 12463) ∩
    agentEv (paperDesignP 12463) (CentreSources 12463 12463)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12463)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12463) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12463) hτ
  have hC := centreSources_ret_charge_row 12463 (paperDesignP 12463) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12463)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12463) (CentreSources 12463 12463)
  direction : analyticBase ⊆ agentEv (paperDesignP 12463) (DirectionError 12463)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12463)) : Set (Ret 12463) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12463)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12463)}
    (hT : (retDist (paperCentres 12463)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12463)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12463)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12463)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12463)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12463)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12463

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12463 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12463 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12463 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12463 12463 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12463)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12463)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12463
  have hb0 := BstLean.Part150.betaJ_nonneg 12463
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12463 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12463 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12463 * BstLean.Part150.betaJ 12463) * 12463) ≤
      (79373367 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12463)) * 12463 := by gcongr <;> linarith
      _ ≤ ((79373367 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12463 * 12463 *
      (1 + BstLean.Part154.deltaChi 12463 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181704883 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12463 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181704883 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12463 : ℝ) / BstLean.Part154.csC) ≤ (2452343 / 25000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12463 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((2452343 / 25000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12463 : ℝ) * (79373367 / 500000) +
        2 * (1792 / 10000 / 12463) * (181704883 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (2452343 / 25000) *
          (81 / 1000 / 12463 + (1792 / 10000 / 12463) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12463

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12463
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12463 ∧
    1 ≤ gPlus 12463 ∧ gPlus 12463 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12463 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12463 : ℝ) < √(1 - 2 / (12463 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12463 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12463 (gMinus 12463) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12463 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12463 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12463 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12463)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12463 (gMinus 12463) (gPlus 12463)
      (finiteEnergy 12463 12463 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12463 (gMinus 12463) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12463 (gMinus 12463) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12463 (gMinus 12463) (54 / 100))
    (by linarith : energyRatio 12463 (gMinus 12463) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12463 (gMinus 12463) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12463 * kappa (energyRatio 12463 (gMinus 12463) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12463) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12463 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12463 12463 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12463 12463 (11 / 1000) / √12463 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12463)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12463 * kappa (energyRatio 12463 (gMinus 12463) (54 / 100))) +
      2 * √(12 * gPlus 12463) / 12463 + finiteEnergy 12463 12463 (11 / 1000) / √12463 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12463 θ ∧ meanLowerRoot 12463 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12463 - 2 / (12463 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12463 - 2 / (12463 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12463 θ ^ 2 / gPlus 12463) - 2 / (12463 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12463 * (kappa (meanLowerRoot 12463 θ ^ 2 / gPlus 12463) -
        2 / (12463 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12463) / 12463 -
        finiteEnergy 12463 12463 (11 / 1000) / √12463 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12463 θ ^ 2 / gPlus 12463 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12463)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12463 θ ^ 2 / gPlus 12463 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12463)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12463 θ ^ 2 / gPlus 12463 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12463 ^ 2 ≤
      kappa (meanLowerRoot 12463 θ ^ 2 / gPlus 12463) - 2 / (12463 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12463 *
      (kappa (meanLowerRoot 12463 θ ^ 2 / gPlus 12463) - 2 / (12463 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12463 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12463)
    linarith
  have ht : √(12 * gPlus 12463) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12463 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12463 12463 (11 / 1000) / √12463 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12463)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12463 (gMinus 12463) (gPlus 12463)
      (finiteEnergy 12463 12463 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12463) (hτ : 0 < (paperDesignP 12463).tau0 c) :
    eR c = (2 / (mA 12463 : ℝ)) *
      normSq (BstLean.Part150.bT 12463 12463 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12463).tau0 c)) /
      (2 / (12463 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12463).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12463).tau0 c))⁻¹ •
      BstLean.Part150.bT 12463 12463 (A1 c) (A2 c) c.1.2 ((paperDesignP 12463).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12463 : ℝ)) * normSq (bR c) / (2 / (12463 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12463}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12463) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12463).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12463 : ℝ) * (paperDesignP 12463).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12463 12463 c.1.2 ((paperDesignP 12463).tau0 c) :=
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

end BstLean.Part266.Row12463

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12464 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12464).real (BstLean.Part211.CentreSource 12464 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12464) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12464 160 (6 / 1000)
  have hj := jS_160_le (n := 12464) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12464 160 (6 / 1000) ^ 2 * 12464 /
      (((12464 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12464 160 (6 / 1000) ^ 2 * 12464 /
      (((12464 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12464 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12464 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12464) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12464 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12464

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12464) :=
  Ethm (paperCentres 12464) ∩ Ethp (paperCentres 12464)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12464)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12464)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12464) (paperCentres 12464)
  have he : exp (-(45 / 10000 * (12464 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12464 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12464) :=
  (passEvent ∩ agentEv (paperDesignP 12464) (DirectionError 12464) ∩
    agentEv (paperDesignP 12464) (CentreSources 12464 12464)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12464)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12464) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12464) hτ
  have hC := centreSources_ret_charge_row 12464 (paperDesignP 12464) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12464)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12464) (CentreSources 12464 12464)
  direction : analyticBase ⊆ agentEv (paperDesignP 12464) (DirectionError 12464)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12464)) : Set (Ret 12464) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12464)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12464)}
    (hT : (retDist (paperCentres 12464)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12464)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12464)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12464)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12464)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12464)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12464

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12464 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12464 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12464 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12464 12464 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12464)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12464)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12464
  have hb0 := BstLean.Part150.betaJ_nonneg 12464
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12464 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12464 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12464 * BstLean.Part150.betaJ 12464) * 12464) ≤
      (158753103 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12464)) * 12464 := by gcongr <;> linarith
      _ ≤ ((158753103 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12464 * 12464 *
      (1 + BstLean.Part154.deltaChi 12464 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181712173 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12464 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181712173 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12464 : ℝ) / BstLean.Part154.csC) ≤ (19619531 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12464 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19619531 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12464 : ℝ) * (158753103 / 1000000) +
        2 * (1792 / 10000 / 12464) * (181712173 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (19619531 / 200000) *
          (81 / 1000 / 12464 + (1792 / 10000 / 12464) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12464

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12464
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12464 ∧
    1 ≤ gPlus 12464 ∧ gPlus 12464 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12464 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12464 : ℝ) < √(1 - 2 / (12464 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12464 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12464 (gMinus 12464) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12464 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12464 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12464 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12464)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12464 (gMinus 12464) (gPlus 12464)
      (finiteEnergy 12464 12464 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12464 (gMinus 12464) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12464 (gMinus 12464) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12464 (gMinus 12464) (54 / 100))
    (by linarith : energyRatio 12464 (gMinus 12464) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12464 (gMinus 12464) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12464 * kappa (energyRatio 12464 (gMinus 12464) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12464) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12464 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12464 12464 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12464 12464 (11 / 1000) / √12464 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12464)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12464 * kappa (energyRatio 12464 (gMinus 12464) (54 / 100))) +
      2 * √(12 * gPlus 12464) / 12464 + finiteEnergy 12464 12464 (11 / 1000) / √12464 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12464 θ ∧ meanLowerRoot 12464 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12464 - 2 / (12464 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12464 - 2 / (12464 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12464 θ ^ 2 / gPlus 12464) - 2 / (12464 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12464 * (kappa (meanLowerRoot 12464 θ ^ 2 / gPlus 12464) -
        2 / (12464 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12464) / 12464 -
        finiteEnergy 12464 12464 (11 / 1000) / √12464 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12464 θ ^ 2 / gPlus 12464 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12464)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12464 θ ^ 2 / gPlus 12464 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12464)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12464 θ ^ 2 / gPlus 12464 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12464 ^ 2 ≤
      kappa (meanLowerRoot 12464 θ ^ 2 / gPlus 12464) - 2 / (12464 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12464 *
      (kappa (meanLowerRoot 12464 θ ^ 2 / gPlus 12464) - 2 / (12464 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12464 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12464)
    linarith
  have ht : √(12 * gPlus 12464) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12464 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12464 12464 (11 / 1000) / √12464 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12464)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12464 (gMinus 12464) (gPlus 12464)
      (finiteEnergy 12464 12464 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12464) (hτ : 0 < (paperDesignP 12464).tau0 c) :
    eR c = (2 / (mA 12464 : ℝ)) *
      normSq (BstLean.Part150.bT 12464 12464 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12464).tau0 c)) /
      (2 / (12464 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12464).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12464).tau0 c))⁻¹ •
      BstLean.Part150.bT 12464 12464 (A1 c) (A2 c) c.1.2 ((paperDesignP 12464).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12464 : ℝ)) * normSq (bR c) / (2 / (12464 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12464}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12464) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12464).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12464 : ℝ) * (paperDesignP 12464).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12464 12464 c.1.2 ((paperDesignP 12464).tau0 c) :=
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

end BstLean.Part266.Row12464

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12465 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12465).real (BstLean.Part211.CentreSource 12465 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12465) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12465 160 (6 / 1000)
  have hj := jS_160_le (n := 12465) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12465 160 (6 / 1000) ^ 2 * 12465 /
      (((12465 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12465 160 (6 / 1000) ^ 2 * 12465 /
      (((12465 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12465 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12465 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12465) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12465 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12465

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12465) :=
  Ethm (paperCentres 12465) ∩ Ethp (paperCentres 12465)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12465)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12465)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12465) (paperCentres 12465)
  have he : exp (-(45 / 10000 * (12465 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12465 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12465) :=
  (passEvent ∩ agentEv (paperDesignP 12465) (DirectionError 12465) ∩
    agentEv (paperDesignP 12465) (CentreSources 12465 12465)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12465)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12465) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12465) hτ
  have hC := centreSources_ret_charge_row 12465 (paperDesignP 12465) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12465)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12465) (CentreSources 12465 12465)
  direction : analyticBase ⊆ agentEv (paperDesignP 12465) (DirectionError 12465)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12465)) : Set (Ret 12465) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12465)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12465)}
    (hT : (retDist (paperCentres 12465)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12465)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12465)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12465)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12465)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12465)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12465

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12465 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12465 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12465 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12465 12465 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12465)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12465)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12465
  have hb0 := BstLean.Part150.betaJ_nonneg 12465
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12465 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12465 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12465 * BstLean.Part150.betaJ 12465) * 12465) ≤
      (158759471 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12465)) * 12465 := by gcongr <;> linarith
      _ ≤ ((158759471 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12465 * 12465 *
      (1 + BstLean.Part154.deltaChi 12465 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90859731 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12465 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90859731 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12465 : ℝ) / BstLean.Part154.csC) ≤ (98101591 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12465 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98101591 / 1000000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12465 : ℝ) * (158759471 / 1000000) +
        2 * (1792 / 10000 / 12465) * (90859731 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (98101591 / 1000000) *
          (81 / 1000 / 12465 + (1792 / 10000 / 12465) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12465

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12465
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12465 ∧
    1 ≤ gPlus 12465 ∧ gPlus 12465 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12465 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12465 : ℝ) < √(1 - 2 / (12465 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12465 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12465 (gMinus 12465) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12465 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12465 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12465 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12465)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12465 (gMinus 12465) (gPlus 12465)
      (finiteEnergy 12465 12465 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12465 (gMinus 12465) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12465 (gMinus 12465) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12465 (gMinus 12465) (54 / 100))
    (by linarith : energyRatio 12465 (gMinus 12465) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12465 (gMinus 12465) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12465 * kappa (energyRatio 12465 (gMinus 12465) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12465) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12465 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12465 12465 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12465 12465 (11 / 1000) / √12465 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12465)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12465 * kappa (energyRatio 12465 (gMinus 12465) (54 / 100))) +
      2 * √(12 * gPlus 12465) / 12465 + finiteEnergy 12465 12465 (11 / 1000) / √12465 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12465 θ ∧ meanLowerRoot 12465 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12465 - 2 / (12465 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12465 - 2 / (12465 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12465 θ ^ 2 / gPlus 12465) - 2 / (12465 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12465 * (kappa (meanLowerRoot 12465 θ ^ 2 / gPlus 12465) -
        2 / (12465 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12465) / 12465 -
        finiteEnergy 12465 12465 (11 / 1000) / √12465 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12465 θ ^ 2 / gPlus 12465 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12465)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12465 θ ^ 2 / gPlus 12465 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12465)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12465 θ ^ 2 / gPlus 12465 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12465 ^ 2 ≤
      kappa (meanLowerRoot 12465 θ ^ 2 / gPlus 12465) - 2 / (12465 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12465 *
      (kappa (meanLowerRoot 12465 θ ^ 2 / gPlus 12465) - 2 / (12465 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12465 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12465)
    linarith
  have ht : √(12 * gPlus 12465) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12465 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12465 12465 (11 / 1000) / √12465 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12465)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12465 (gMinus 12465) (gPlus 12465)
      (finiteEnergy 12465 12465 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12465) (hτ : 0 < (paperDesignP 12465).tau0 c) :
    eR c = (2 / (mA 12465 : ℝ)) *
      normSq (BstLean.Part150.bT 12465 12465 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12465).tau0 c)) /
      (2 / (12465 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12465).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12465).tau0 c))⁻¹ •
      BstLean.Part150.bT 12465 12465 (A1 c) (A2 c) c.1.2 ((paperDesignP 12465).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12465 : ℝ)) * normSq (bR c) / (2 / (12465 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12465}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12465) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12465).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12465 : ℝ) * (paperDesignP 12465).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12465 12465 c.1.2 ((paperDesignP 12465).tau0 c) :=
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

end BstLean.Part266.Row12465

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12466 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12466).real (BstLean.Part211.CentreSource 12466 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12466) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12466 160 (6 / 1000)
  have hj := jS_160_le (n := 12466) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12466 160 (6 / 1000) ^ 2 * 12466 /
      (((12466 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12466 160 (6 / 1000) ^ 2 * 12466 /
      (((12466 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12466 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12466 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12466) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12466 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12466

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12466) :=
  Ethm (paperCentres 12466) ∩ Ethp (paperCentres 12466)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12466)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12466)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12466) (paperCentres 12466)
  have he : exp (-(45 / 10000 * (12466 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12466 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12466) :=
  (passEvent ∩ agentEv (paperDesignP 12466) (DirectionError 12466) ∩
    agentEv (paperDesignP 12466) (CentreSources 12466 12466)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12466)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12466) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12466) hτ
  have hC := centreSources_ret_charge_row 12466 (paperDesignP 12466) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12466)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12466) (CentreSources 12466 12466)
  direction : analyticBase ⊆ agentEv (paperDesignP 12466) (DirectionError 12466)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12466)) : Set (Ret 12466) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12466)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12466)}
    (hT : (retDist (paperCentres 12466)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12466)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12466)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12466)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12466)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12466)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12466

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12466 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12466 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12466 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12466 12466 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12466)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12466)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12466
  have hb0 := BstLean.Part150.betaJ_nonneg 12466
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12466 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12466 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12466 * BstLean.Part150.betaJ 12466) * 12466) ≤
      (158765839 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12466)) * 12466 := by gcongr <;> linarith
      _ ≤ ((158765839 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12466 * 12466 *
      (1 + BstLean.Part154.deltaChi 12466 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181726751 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12466 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181726751 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12466 : ℝ) / BstLean.Part154.csC) ≤ (49052763 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12466 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((49052763 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12466 : ℝ) * (158765839 / 1000000) +
        2 * (1792 / 10000 / 12466) * (181726751 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (49052763 / 500000) *
          (81 / 1000 / 12466 + (1792 / 10000 / 12466) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12466

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12466
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12466 ∧
    1 ≤ gPlus 12466 ∧ gPlus 12466 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12466 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12466 : ℝ) < √(1 - 2 / (12466 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12466 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12466 (gMinus 12466) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12466 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12466 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12466 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12466)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12466 (gMinus 12466) (gPlus 12466)
      (finiteEnergy 12466 12466 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12466 (gMinus 12466) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12466 (gMinus 12466) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12466 (gMinus 12466) (54 / 100))
    (by linarith : energyRatio 12466 (gMinus 12466) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12466 (gMinus 12466) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12466 * kappa (energyRatio 12466 (gMinus 12466) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12466) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12466 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12466 12466 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12466 12466 (11 / 1000) / √12466 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12466)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12466 * kappa (energyRatio 12466 (gMinus 12466) (54 / 100))) +
      2 * √(12 * gPlus 12466) / 12466 + finiteEnergy 12466 12466 (11 / 1000) / √12466 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12466 θ ∧ meanLowerRoot 12466 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12466 - 2 / (12466 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12466 - 2 / (12466 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12466 θ ^ 2 / gPlus 12466) - 2 / (12466 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12466 * (kappa (meanLowerRoot 12466 θ ^ 2 / gPlus 12466) -
        2 / (12466 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12466) / 12466 -
        finiteEnergy 12466 12466 (11 / 1000) / √12466 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12466 θ ^ 2 / gPlus 12466 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12466)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12466 θ ^ 2 / gPlus 12466 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12466)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12466 θ ^ 2 / gPlus 12466 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12466 ^ 2 ≤
      kappa (meanLowerRoot 12466 θ ^ 2 / gPlus 12466) - 2 / (12466 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12466 *
      (kappa (meanLowerRoot 12466 θ ^ 2 / gPlus 12466) - 2 / (12466 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12466 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12466)
    linarith
  have ht : √(12 * gPlus 12466) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12466 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12466 12466 (11 / 1000) / √12466 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12466)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12466 (gMinus 12466) (gPlus 12466)
      (finiteEnergy 12466 12466 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12466) (hτ : 0 < (paperDesignP 12466).tau0 c) :
    eR c = (2 / (mA 12466 : ℝ)) *
      normSq (BstLean.Part150.bT 12466 12466 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12466).tau0 c)) /
      (2 / (12466 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12466).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12466).tau0 c))⁻¹ •
      BstLean.Part150.bT 12466 12466 (A1 c) (A2 c) c.1.2 ((paperDesignP 12466).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12466 : ℝ)) * normSq (bR c) / (2 / (12466 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12466}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12466) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12466).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12466 : ℝ) * (paperDesignP 12466).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12466 12466 c.1.2 ((paperDesignP 12466).tau0 c) :=
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

end BstLean.Part266.Row12466

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12467 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12467).real (BstLean.Part211.CentreSource 12467 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12467) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12467 160 (6 / 1000)
  have hj := jS_160_le (n := 12467) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12467 160 (6 / 1000) ^ 2 * 12467 /
      (((12467 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12467 160 (6 / 1000) ^ 2 * 12467 /
      (((12467 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12467 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12467 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12467) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12467 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12467

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12467) :=
  Ethm (paperCentres 12467) ∩ Ethp (paperCentres 12467)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12467)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12467)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12467) (paperCentres 12467)
  have he : exp (-(45 / 10000 * (12467 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12467 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12467) :=
  (passEvent ∩ agentEv (paperDesignP 12467) (DirectionError 12467) ∩
    agentEv (paperDesignP 12467) (CentreSources 12467 12467)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12467)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12467) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12467) hτ
  have hC := centreSources_ret_charge_row 12467 (paperDesignP 12467) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12467)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12467) (CentreSources 12467 12467)
  direction : analyticBase ⊆ agentEv (paperDesignP 12467) (DirectionError 12467)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12467)) : Set (Ret 12467) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12467)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12467)}
    (hT : (retDist (paperCentres 12467)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12467)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12467)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12467)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12467)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12467)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12467

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12467 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12467 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12467 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12467 12467 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12467)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12467)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12467
  have hb0 := BstLean.Part150.betaJ_nonneg 12467
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12467 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12467 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12467 * BstLean.Part150.betaJ 12467) * 12467) ≤
      (158772207 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12467)) * 12467 := by gcongr <;> linarith
      _ ≤ ((158772207 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12467 * 12467 *
      (1 + BstLean.Part154.deltaChi 12467 12 + 2 / π) / BstLean.Part154.csC) ≤
      (4543351 / 25000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12467 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((4543351 / 25000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12467 : ℝ) / BstLean.Part154.csC) ≤ (4905473 / 50000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12467 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((4905473 / 50000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12467 : ℝ) * (158772207 / 1000000) +
        2 * (1792 / 10000 / 12467) * (4543351 / 25000) +
        4 * (1 / 2.506628) * 1.036505 * (4905473 / 50000) *
          (81 / 1000 / 12467 + (1792 / 10000 / 12467) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12467

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12467
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12467 ∧
    1 ≤ gPlus 12467 ∧ gPlus 12467 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12467 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12467 : ℝ) < √(1 - 2 / (12467 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12467 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12467 (gMinus 12467) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12467 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12467 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12467 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12467)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12467 (gMinus 12467) (gPlus 12467)
      (finiteEnergy 12467 12467 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12467 (gMinus 12467) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12467 (gMinus 12467) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12467 (gMinus 12467) (54 / 100))
    (by linarith : energyRatio 12467 (gMinus 12467) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12467 (gMinus 12467) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12467 * kappa (energyRatio 12467 (gMinus 12467) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12467) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12467 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12467 12467 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12467 12467 (11 / 1000) / √12467 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12467)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12467 * kappa (energyRatio 12467 (gMinus 12467) (54 / 100))) +
      2 * √(12 * gPlus 12467) / 12467 + finiteEnergy 12467 12467 (11 / 1000) / √12467 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12467 θ ∧ meanLowerRoot 12467 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12467 - 2 / (12467 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12467 - 2 / (12467 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12467 θ ^ 2 / gPlus 12467) - 2 / (12467 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12467 * (kappa (meanLowerRoot 12467 θ ^ 2 / gPlus 12467) -
        2 / (12467 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12467) / 12467 -
        finiteEnergy 12467 12467 (11 / 1000) / √12467 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12467 θ ^ 2 / gPlus 12467 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12467)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12467 θ ^ 2 / gPlus 12467 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12467)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12467 θ ^ 2 / gPlus 12467 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12467 ^ 2 ≤
      kappa (meanLowerRoot 12467 θ ^ 2 / gPlus 12467) - 2 / (12467 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12467 *
      (kappa (meanLowerRoot 12467 θ ^ 2 / gPlus 12467) - 2 / (12467 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12467 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12467)
    linarith
  have ht : √(12 * gPlus 12467) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12467 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12467 12467 (11 / 1000) / √12467 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12467)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12467 (gMinus 12467) (gPlus 12467)
      (finiteEnergy 12467 12467 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12467) (hτ : 0 < (paperDesignP 12467).tau0 c) :
    eR c = (2 / (mA 12467 : ℝ)) *
      normSq (BstLean.Part150.bT 12467 12467 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12467).tau0 c)) /
      (2 / (12467 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12467).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12467).tau0 c))⁻¹ •
      BstLean.Part150.bT 12467 12467 (A1 c) (A2 c) c.1.2 ((paperDesignP 12467).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12467 : ℝ)) * normSq (bR c) / (2 / (12467 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12467}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12467) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12467).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12467 : ℝ) * (paperDesignP 12467).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12467 12467 c.1.2 ((paperDesignP 12467).tau0 c) :=
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

end BstLean.Part266.Row12467

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12468 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12468).real (BstLean.Part211.CentreSource 12468 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12468) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12468 160 (6 / 1000)
  have hj := jS_160_le (n := 12468) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12468 160 (6 / 1000) ^ 2 * 12468 /
      (((12468 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12468 160 (6 / 1000) ^ 2 * 12468 /
      (((12468 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12468 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12468 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12468) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12468 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12468

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12468) :=
  Ethm (paperCentres 12468) ∩ Ethp (paperCentres 12468)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12468)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12468)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12468) (paperCentres 12468)
  have he : exp (-(45 / 10000 * (12468 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12468 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12468) :=
  (passEvent ∩ agentEv (paperDesignP 12468) (DirectionError 12468) ∩
    agentEv (paperDesignP 12468) (CentreSources 12468 12468)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12468)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12468) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12468) hτ
  have hC := centreSources_ret_charge_row 12468 (paperDesignP 12468) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12468)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12468) (CentreSources 12468 12468)
  direction : analyticBase ⊆ agentEv (paperDesignP 12468) (DirectionError 12468)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12468)) : Set (Ret 12468) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12468)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12468)}
    (hT : (retDist (paperCentres 12468)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12468)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12468)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12468)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12468)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12468)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12468

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12468 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12468 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12468 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12468 12468 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12468)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12468)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12468
  have hb0 := BstLean.Part150.betaJ_nonneg 12468
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12468 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12468 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12468 * BstLean.Part150.betaJ 12468) * 12468) ≤
      (79389287 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12468)) * 12468 := by gcongr <;> linarith
      _ ≤ ((79389287 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12468 * 12468 *
      (1 + BstLean.Part154.deltaChi 12468 12 + 2 / π) / BstLean.Part154.csC) ≤
      (11358833 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12468 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((11358833 / 62500) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12468 : ℝ) / BstLean.Part154.csC) ≤ (19622679 / 200000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12468 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((19622679 / 200000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12468 : ℝ) * (79389287 / 500000) +
        2 * (1792 / 10000 / 12468) * (11358833 / 62500) +
        4 * (1 / 2.506628) * 1.036505 * (19622679 / 200000) *
          (81 / 1000 / 12468 + (1792 / 10000 / 12468) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12468

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12468
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12468 ∧
    1 ≤ gPlus 12468 ∧ gPlus 12468 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12468 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12468 : ℝ) < √(1 - 2 / (12468 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12468 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12468 (gMinus 12468) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12468 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12468 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12468 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12468)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12468 (gMinus 12468) (gPlus 12468)
      (finiteEnergy 12468 12468 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12468 (gMinus 12468) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12468 (gMinus 12468) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12468 (gMinus 12468) (54 / 100))
    (by linarith : energyRatio 12468 (gMinus 12468) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12468 (gMinus 12468) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12468 * kappa (energyRatio 12468 (gMinus 12468) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12468) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12468 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12468 12468 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12468 12468 (11 / 1000) / √12468 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12468)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12468 * kappa (energyRatio 12468 (gMinus 12468) (54 / 100))) +
      2 * √(12 * gPlus 12468) / 12468 + finiteEnergy 12468 12468 (11 / 1000) / √12468 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12468 θ ∧ meanLowerRoot 12468 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12468 - 2 / (12468 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12468 - 2 / (12468 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12468 θ ^ 2 / gPlus 12468) - 2 / (12468 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12468 * (kappa (meanLowerRoot 12468 θ ^ 2 / gPlus 12468) -
        2 / (12468 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12468) / 12468 -
        finiteEnergy 12468 12468 (11 / 1000) / √12468 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12468 θ ^ 2 / gPlus 12468 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12468)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12468 θ ^ 2 / gPlus 12468 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12468)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12468 θ ^ 2 / gPlus 12468 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12468 ^ 2 ≤
      kappa (meanLowerRoot 12468 θ ^ 2 / gPlus 12468) - 2 / (12468 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12468 *
      (kappa (meanLowerRoot 12468 θ ^ 2 / gPlus 12468) - 2 / (12468 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12468 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12468)
    linarith
  have ht : √(12 * gPlus 12468) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12468 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12468 12468 (11 / 1000) / √12468 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12468)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12468 (gMinus 12468) (gPlus 12468)
      (finiteEnergy 12468 12468 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12468) (hτ : 0 < (paperDesignP 12468).tau0 c) :
    eR c = (2 / (mA 12468 : ℝ)) *
      normSq (BstLean.Part150.bT 12468 12468 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12468).tau0 c)) /
      (2 / (12468 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12468).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12468).tau0 c))⁻¹ •
      BstLean.Part150.bT 12468 12468 (A1 c) (A2 c) c.1.2 ((paperDesignP 12468).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12468 : ℝ)) * normSq (bR c) / (2 / (12468 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12468}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12468) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12468).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12468 : ℝ) * (paperDesignP 12468).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12468 12468 c.1.2 ((paperDesignP 12468).tau0 c) :=
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

end BstLean.Part266.Row12468

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12469 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12469).real (BstLean.Part211.CentreSource 12469 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12469) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12469 160 (6 / 1000)
  have hj := jS_160_le (n := 12469) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12469 160 (6 / 1000) ^ 2 * 12469 /
      (((12469 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12469 160 (6 / 1000) ^ 2 * 12469 /
      (((12469 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12469 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12469 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12469) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12469 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12469

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12469) :=
  Ethm (paperCentres 12469) ∩ Ethp (paperCentres 12469)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12469)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12469)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12469) (paperCentres 12469)
  have he : exp (-(45 / 10000 * (12469 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12469 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12469) :=
  (passEvent ∩ agentEv (paperDesignP 12469) (DirectionError 12469) ∩
    agentEv (paperDesignP 12469) (CentreSources 12469 12469)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12469)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12469) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12469) hτ
  have hC := centreSources_ret_charge_row 12469 (paperDesignP 12469) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12469)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12469) (CentreSources 12469 12469)
  direction : analyticBase ⊆ agentEv (paperDesignP 12469) (DirectionError 12469)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12469)) : Set (Ret 12469) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12469)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12469)}
    (hT : (retDist (paperCentres 12469)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12469)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12469)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12469)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12469)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12469)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12469

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12469 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12469 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12469 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12469 12469 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12469)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12469)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12469
  have hb0 := BstLean.Part150.betaJ_nonneg 12469
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12469 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12469 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12469 * BstLean.Part150.betaJ 12469) * 12469) ≤
      (79392471 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12469)) * 12469 := by gcongr <;> linarith
      _ ≤ ((79392471 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12469 * 12469 *
      (1 + BstLean.Part154.deltaChi 12469 12 + 2 / π) / BstLean.Part154.csC) ≤
      (22718577 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12469 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((22718577 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12469 : ℝ) / BstLean.Part154.csC) ≤ (9811733 / 100000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12469 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((9811733 / 100000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12469 : ℝ) * (79392471 / 500000) +
        2 * (1792 / 10000 / 12469) * (22718577 / 125000) +
        4 * (1 / 2.506628) * 1.036505 * (9811733 / 100000) *
          (81 / 1000 / 12469 + (1792 / 10000 / 12469) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12469

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12469
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12469 ∧
    1 ≤ gPlus 12469 ∧ gPlus 12469 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12469 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12469 : ℝ) < √(1 - 2 / (12469 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12469 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12469 (gMinus 12469) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12469 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12469 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12469 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12469)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12469 (gMinus 12469) (gPlus 12469)
      (finiteEnergy 12469 12469 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12469 (gMinus 12469) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12469 (gMinus 12469) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12469 (gMinus 12469) (54 / 100))
    (by linarith : energyRatio 12469 (gMinus 12469) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12469 (gMinus 12469) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12469 * kappa (energyRatio 12469 (gMinus 12469) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12469) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12469 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12469 12469 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12469 12469 (11 / 1000) / √12469 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12469)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12469 * kappa (energyRatio 12469 (gMinus 12469) (54 / 100))) +
      2 * √(12 * gPlus 12469) / 12469 + finiteEnergy 12469 12469 (11 / 1000) / √12469 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12469 θ ∧ meanLowerRoot 12469 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12469 - 2 / (12469 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12469 - 2 / (12469 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12469 θ ^ 2 / gPlus 12469) - 2 / (12469 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12469 * (kappa (meanLowerRoot 12469 θ ^ 2 / gPlus 12469) -
        2 / (12469 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12469) / 12469 -
        finiteEnergy 12469 12469 (11 / 1000) / √12469 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12469 θ ^ 2 / gPlus 12469 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12469)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12469 θ ^ 2 / gPlus 12469 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12469)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12469 θ ^ 2 / gPlus 12469 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12469 ^ 2 ≤
      kappa (meanLowerRoot 12469 θ ^ 2 / gPlus 12469) - 2 / (12469 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12469 *
      (kappa (meanLowerRoot 12469 θ ^ 2 / gPlus 12469) - 2 / (12469 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12469 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12469)
    linarith
  have ht : √(12 * gPlus 12469) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12469 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12469 12469 (11 / 1000) / √12469 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12469)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12469 (gMinus 12469) (gPlus 12469)
      (finiteEnergy 12469 12469 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12469) (hτ : 0 < (paperDesignP 12469).tau0 c) :
    eR c = (2 / (mA 12469 : ℝ)) *
      normSq (BstLean.Part150.bT 12469 12469 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12469).tau0 c)) /
      (2 / (12469 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12469).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12469).tau0 c))⁻¹ •
      BstLean.Part150.bT 12469 12469 (A1 c) (A2 c) c.1.2 ((paperDesignP 12469).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12469 : ℝ)) * normSq (bR c) / (2 / (12469 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12469}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12469) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12469).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12469 : ℝ) * (paperDesignP 12469).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12469 12469 c.1.2 ((paperDesignP 12469).tau0 c) :=
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

end BstLean.Part266.Row12469

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12470 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12470).real (BstLean.Part211.CentreSource 12470 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12470) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12470 160 (6 / 1000)
  have hj := jS_160_le (n := 12470) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12470 160 (6 / 1000) ^ 2 * 12470 /
      (((12470 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12470 160 (6 / 1000) ^ 2 * 12470 /
      (((12470 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12470 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12470 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12470) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12470 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12470

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12470) :=
  Ethm (paperCentres 12470) ∩ Ethp (paperCentres 12470)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12470)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12470)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12470) (paperCentres 12470)
  have he : exp (-(45 / 10000 * (12470 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12470 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12470) :=
  (passEvent ∩ agentEv (paperDesignP 12470) (DirectionError 12470) ∩
    agentEv (paperDesignP 12470) (CentreSources 12470 12470)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12470)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12470) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12470) hτ
  have hC := centreSources_ret_charge_row 12470 (paperDesignP 12470) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12470)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12470) (CentreSources 12470 12470)
  direction : analyticBase ⊆ agentEv (paperDesignP 12470) (DirectionError 12470)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12470)) : Set (Ret 12470) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12470)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12470)}
    (hT : (retDist (paperCentres 12470)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12470)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12470)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12470)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12470)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12470)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12470

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12470 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12470 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12470 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12470 12470 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12470)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12470)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12470
  have hb0 := BstLean.Part150.betaJ_nonneg 12470
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12470 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12470 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12470 * BstLean.Part150.betaJ 12470) * 12470) ≤
      (158791309 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12470)) * 12470 := by gcongr <;> linarith
      _ ≤ ((158791309 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12470 * 12470 *
      (1 + BstLean.Part154.deltaChi 12470 12 + 2 / π) / BstLean.Part154.csC) ≤
      (2839936 / 15625) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12470 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((2839936 / 15625) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12470 : ℝ) / BstLean.Part154.csC) ≤ (6132579 / 62500) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12470 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((6132579 / 62500) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12470 : ℝ) * (158791309 / 1000000) +
        2 * (1792 / 10000 / 12470) * (2839936 / 15625) +
        4 * (1 / 2.506628) * 1.036505 * (6132579 / 62500) *
          (81 / 1000 / 12470 + (1792 / 10000 / 12470) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12470

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12470
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12470 ∧
    1 ≤ gPlus 12470 ∧ gPlus 12470 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12470 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12470 : ℝ) < √(1 - 2 / (12470 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12470 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12470 (gMinus 12470) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12470 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12470 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12470 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12470)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12470 (gMinus 12470) (gPlus 12470)
      (finiteEnergy 12470 12470 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12470 (gMinus 12470) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12470 (gMinus 12470) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12470 (gMinus 12470) (54 / 100))
    (by linarith : energyRatio 12470 (gMinus 12470) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12470 (gMinus 12470) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12470 * kappa (energyRatio 12470 (gMinus 12470) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12470) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12470 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12470 12470 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12470 12470 (11 / 1000) / √12470 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12470)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12470 * kappa (energyRatio 12470 (gMinus 12470) (54 / 100))) +
      2 * √(12 * gPlus 12470) / 12470 + finiteEnergy 12470 12470 (11 / 1000) / √12470 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12470 θ ∧ meanLowerRoot 12470 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12470 - 2 / (12470 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12470 - 2 / (12470 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12470 θ ^ 2 / gPlus 12470) - 2 / (12470 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12470 * (kappa (meanLowerRoot 12470 θ ^ 2 / gPlus 12470) -
        2 / (12470 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12470) / 12470 -
        finiteEnergy 12470 12470 (11 / 1000) / √12470 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12470 θ ^ 2 / gPlus 12470 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12470)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12470 θ ^ 2 / gPlus 12470 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12470)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12470 θ ^ 2 / gPlus 12470 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12470 ^ 2 ≤
      kappa (meanLowerRoot 12470 θ ^ 2 / gPlus 12470) - 2 / (12470 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12470 *
      (kappa (meanLowerRoot 12470 θ ^ 2 / gPlus 12470) - 2 / (12470 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12470 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12470)
    linarith
  have ht : √(12 * gPlus 12470) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12470 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12470 12470 (11 / 1000) / √12470 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12470)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12470 (gMinus 12470) (gPlus 12470)
      (finiteEnergy 12470 12470 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12470) (hτ : 0 < (paperDesignP 12470).tau0 c) :
    eR c = (2 / (mA 12470 : ℝ)) *
      normSq (BstLean.Part150.bT 12470 12470 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12470).tau0 c)) /
      (2 / (12470 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12470).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12470).tau0 c))⁻¹ •
      BstLean.Part150.bT 12470 12470 (A1 c) (A2 c) c.1.2 ((paperDesignP 12470).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12470 : ℝ)) * normSq (bR c) / (2 / (12470 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12470}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12470) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12470).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12470 : ℝ) * (paperDesignP 12470).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12470 12470 c.1.2 ((paperDesignP 12470).tau0 c) :=
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

end BstLean.Part266.Row12470

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12471 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12471).real (BstLean.Part211.CentreSource 12471 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12471) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12471 160 (6 / 1000)
  have hj := jS_160_le (n := 12471) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12471 160 (6 / 1000) ^ 2 * 12471 /
      (((12471 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12471 160 (6 / 1000) ^ 2 * 12471 /
      (((12471 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12471 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12471 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12471) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12471 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12471

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12471) :=
  Ethm (paperCentres 12471) ∩ Ethp (paperCentres 12471)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12471)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12471)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12471) (paperCentres 12471)
  have he : exp (-(45 / 10000 * (12471 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12471 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12471) :=
  (passEvent ∩ agentEv (paperDesignP 12471) (DirectionError 12471) ∩
    agentEv (paperDesignP 12471) (CentreSources 12471 12471)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12471)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12471) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12471) hτ
  have hC := centreSources_ret_charge_row 12471 (paperDesignP 12471) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12471)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12471) (CentreSources 12471 12471)
  direction : analyticBase ⊆ agentEv (paperDesignP 12471) (DirectionError 12471)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12471)) : Set (Ret 12471) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12471)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12471)}
    (hT : (retDist (paperCentres 12471)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12471)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12471)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12471)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12471)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12471)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12471

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12471 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12471 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12471 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12471 12471 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12471)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12471)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12471
  have hb0 := BstLean.Part150.betaJ_nonneg 12471
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12471 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12471 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12471 * BstLean.Part150.betaJ 12471) * 12471) ≤
      (6351907 / 40000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12471)) * 12471 := by gcongr <;> linarith
      _ ≤ ((6351907 / 40000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12471 * 12471 *
      (1 + BstLean.Part154.deltaChi 12471 12 + 2 / π) / BstLean.Part154.csC) ≤
      (22720399 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12471 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((22720399 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12471 : ℝ) / BstLean.Part154.csC) ≤ (49062599 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12471 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((49062599 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12471 : ℝ) * (6351907 / 40000) +
        2 * (1792 / 10000 / 12471) * (22720399 / 125000) +
        4 * (1 / 2.506628) * 1.036505 * (49062599 / 500000) *
          (81 / 1000 / 12471 + (1792 / 10000 / 12471) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12471

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12471
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12471 ∧
    1 ≤ gPlus 12471 ∧ gPlus 12471 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12471 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12471 : ℝ) < √(1 - 2 / (12471 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12471 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12471 (gMinus 12471) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12471 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12471 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12471 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12471)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12471 (gMinus 12471) (gPlus 12471)
      (finiteEnergy 12471 12471 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12471 (gMinus 12471) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12471 (gMinus 12471) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12471 (gMinus 12471) (54 / 100))
    (by linarith : energyRatio 12471 (gMinus 12471) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12471 (gMinus 12471) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12471 * kappa (energyRatio 12471 (gMinus 12471) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12471) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12471 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12471 12471 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12471 12471 (11 / 1000) / √12471 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12471)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12471 * kappa (energyRatio 12471 (gMinus 12471) (54 / 100))) +
      2 * √(12 * gPlus 12471) / 12471 + finiteEnergy 12471 12471 (11 / 1000) / √12471 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12471 θ ∧ meanLowerRoot 12471 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12471 - 2 / (12471 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12471 - 2 / (12471 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12471 θ ^ 2 / gPlus 12471) - 2 / (12471 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12471 * (kappa (meanLowerRoot 12471 θ ^ 2 / gPlus 12471) -
        2 / (12471 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12471) / 12471 -
        finiteEnergy 12471 12471 (11 / 1000) / √12471 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12471 θ ^ 2 / gPlus 12471 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12471)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12471 θ ^ 2 / gPlus 12471 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12471)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12471 θ ^ 2 / gPlus 12471 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12471 ^ 2 ≤
      kappa (meanLowerRoot 12471 θ ^ 2 / gPlus 12471) - 2 / (12471 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12471 *
      (kappa (meanLowerRoot 12471 θ ^ 2 / gPlus 12471) - 2 / (12471 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12471 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12471)
    linarith
  have ht : √(12 * gPlus 12471) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12471 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12471 12471 (11 / 1000) / √12471 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12471)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12471 (gMinus 12471) (gPlus 12471)
      (finiteEnergy 12471 12471 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12471) (hτ : 0 < (paperDesignP 12471).tau0 c) :
    eR c = (2 / (mA 12471 : ℝ)) *
      normSq (BstLean.Part150.bT 12471 12471 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12471).tau0 c)) /
      (2 / (12471 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12471).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12471).tau0 c))⁻¹ •
      BstLean.Part150.bT 12471 12471 (A1 c) (A2 c) c.1.2 ((paperDesignP 12471).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12471 : ℝ)) * normSq (bR c) / (2 / (12471 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12471}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12471) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12471).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12471 : ℝ) * (paperDesignP 12471).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12471 12471 c.1.2 ((paperDesignP 12471).tau0 c) :=
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

end BstLean.Part266.Row12471

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12472 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12472).real (BstLean.Part211.CentreSource 12472 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12472) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12472 160 (6 / 1000)
  have hj := jS_160_le (n := 12472) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12472 160 (6 / 1000) ^ 2 * 12472 /
      (((12472 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12472 160 (6 / 1000) ^ 2 * 12472 /
      (((12472 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12472 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12472 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12472) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12472 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12472

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12472) :=
  Ethm (paperCentres 12472) ∩ Ethp (paperCentres 12472)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12472)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12472)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12472) (paperCentres 12472)
  have he : exp (-(45 / 10000 * (12472 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12472 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12472) :=
  (passEvent ∩ agentEv (paperDesignP 12472) (DirectionError 12472) ∩
    agentEv (paperDesignP 12472) (CentreSources 12472 12472)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12472)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12472) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12472) hτ
  have hC := centreSources_ret_charge_row 12472 (paperDesignP 12472) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12472)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12472) (CentreSources 12472 12472)
  direction : analyticBase ⊆ agentEv (paperDesignP 12472) (DirectionError 12472)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12472)) : Set (Ret 12472) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12472)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12472)}
    (hT : (retDist (paperCentres 12472)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12472)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12472)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12472)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12472)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12472)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12472

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12472 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12472 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12472 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12472 12472 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12472)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12472)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12472
  have hb0 := BstLean.Part150.betaJ_nonneg 12472
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12472 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12472 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12472 * BstLean.Part150.betaJ 12472) * 12472) ≤
      (79402021 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12472)) * 12472 := by gcongr <;> linarith
      _ ≤ ((79402021 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12472 * 12472 *
      (1 + BstLean.Part154.deltaChi 12472 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181770479 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12472 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181770479 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12472 : ℝ) / BstLean.Part154.csC) ≤ (24532283 / 250000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12472 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((24532283 / 250000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12472 : ℝ) * (79402021 / 500000) +
        2 * (1792 / 10000 / 12472) * (181770479 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (24532283 / 250000) *
          (81 / 1000 / 12472 + (1792 / 10000 / 12472) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12472

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12472
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12472 ∧
    1 ≤ gPlus 12472 ∧ gPlus 12472 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12472 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12472 : ℝ) < √(1 - 2 / (12472 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12472 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12472 (gMinus 12472) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12472 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12472 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12472 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12472)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12472 (gMinus 12472) (gPlus 12472)
      (finiteEnergy 12472 12472 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12472 (gMinus 12472) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12472 (gMinus 12472) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12472 (gMinus 12472) (54 / 100))
    (by linarith : energyRatio 12472 (gMinus 12472) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12472 (gMinus 12472) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12472 * kappa (energyRatio 12472 (gMinus 12472) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12472) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12472 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12472 12472 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12472 12472 (11 / 1000) / √12472 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12472)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12472 * kappa (energyRatio 12472 (gMinus 12472) (54 / 100))) +
      2 * √(12 * gPlus 12472) / 12472 + finiteEnergy 12472 12472 (11 / 1000) / √12472 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12472 θ ∧ meanLowerRoot 12472 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12472 - 2 / (12472 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12472 - 2 / (12472 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12472 θ ^ 2 / gPlus 12472) - 2 / (12472 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12472 * (kappa (meanLowerRoot 12472 θ ^ 2 / gPlus 12472) -
        2 / (12472 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12472) / 12472 -
        finiteEnergy 12472 12472 (11 / 1000) / √12472 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12472 θ ^ 2 / gPlus 12472 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12472)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12472 θ ^ 2 / gPlus 12472 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12472)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12472 θ ^ 2 / gPlus 12472 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12472 ^ 2 ≤
      kappa (meanLowerRoot 12472 θ ^ 2 / gPlus 12472) - 2 / (12472 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12472 *
      (kappa (meanLowerRoot 12472 θ ^ 2 / gPlus 12472) - 2 / (12472 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12472 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12472)
    linarith
  have ht : √(12 * gPlus 12472) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12472 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12472 12472 (11 / 1000) / √12472 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12472)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12472 (gMinus 12472) (gPlus 12472)
      (finiteEnergy 12472 12472 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12472) (hτ : 0 < (paperDesignP 12472).tau0 c) :
    eR c = (2 / (mA 12472 : ℝ)) *
      normSq (BstLean.Part150.bT 12472 12472 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12472).tau0 c)) /
      (2 / (12472 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12472).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12472).tau0 c))⁻¹ •
      BstLean.Part150.bT 12472 12472 (A1 c) (A2 c) c.1.2 ((paperDesignP 12472).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12472 : ℝ)) * normSq (bR c) / (2 / (12472 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12472}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12472) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12472).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12472 : ℝ) * (paperDesignP 12472).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12472 12472 c.1.2 ((paperDesignP 12472).tau0 c) :=
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

end BstLean.Part266.Row12472

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12473 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12473).real (BstLean.Part211.CentreSource 12473 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12473) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12473 160 (6 / 1000)
  have hj := jS_160_le (n := 12473) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12473 160 (6 / 1000) ^ 2 * 12473 /
      (((12473 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12473 160 (6 / 1000) ^ 2 * 12473 /
      (((12473 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12473 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12473 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12473) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12473 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12473

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12473) :=
  Ethm (paperCentres 12473) ∩ Ethp (paperCentres 12473)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12473)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12473)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12473) (paperCentres 12473)
  have he : exp (-(45 / 10000 * (12473 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12473 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12473) :=
  (passEvent ∩ agentEv (paperDesignP 12473) (DirectionError 12473) ∩
    agentEv (paperDesignP 12473) (CentreSources 12473 12473)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12473)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12473) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12473) hτ
  have hC := centreSources_ret_charge_row 12473 (paperDesignP 12473) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12473)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12473) (CentreSources 12473 12473)
  direction : analyticBase ⊆ agentEv (paperDesignP 12473) (DirectionError 12473)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12473)) : Set (Ret 12473) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12473)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12473)}
    (hT : (retDist (paperCentres 12473)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12473)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12473)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12473)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12473)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12473)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12473

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12473 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12473 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12473 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12473 12473 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12473)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12473)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12473
  have hb0 := BstLean.Part150.betaJ_nonneg 12473
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12473 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12473 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12473 * BstLean.Part150.betaJ 12473) * 12473) ≤
      (19851301 / 125000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12473)) * 12473 := by gcongr <;> linarith
      _ ≤ ((19851301 / 125000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12473 * 12473 *
      (1 + BstLean.Part154.deltaChi 12473 12 + 2 / π) / BstLean.Part154.csC) ≤
      (90888883 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12473 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((90888883 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12473 : ℝ) / BstLean.Part154.csC) ≤ (49066533 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12473 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((49066533 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12473 : ℝ) * (19851301 / 125000) +
        2 * (1792 / 10000 / 12473) * (90888883 / 500000) +
        4 * (1 / 2.506628) * 1.036505 * (49066533 / 500000) *
          (81 / 1000 / 12473 + (1792 / 10000 / 12473) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12473

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12473
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12473 ∧
    1 ≤ gPlus 12473 ∧ gPlus 12473 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12473 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12473 : ℝ) < √(1 - 2 / (12473 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12473 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12473 (gMinus 12473) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12473 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12473 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12473 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12473)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12473 (gMinus 12473) (gPlus 12473)
      (finiteEnergy 12473 12473 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12473 (gMinus 12473) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12473 (gMinus 12473) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12473 (gMinus 12473) (54 / 100))
    (by linarith : energyRatio 12473 (gMinus 12473) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12473 (gMinus 12473) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12473 * kappa (energyRatio 12473 (gMinus 12473) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12473) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12473 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12473 12473 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12473 12473 (11 / 1000) / √12473 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12473)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12473 * kappa (energyRatio 12473 (gMinus 12473) (54 / 100))) +
      2 * √(12 * gPlus 12473) / 12473 + finiteEnergy 12473 12473 (11 / 1000) / √12473 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12473 θ ∧ meanLowerRoot 12473 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12473 - 2 / (12473 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12473 - 2 / (12473 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12473 θ ^ 2 / gPlus 12473) - 2 / (12473 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12473 * (kappa (meanLowerRoot 12473 θ ^ 2 / gPlus 12473) -
        2 / (12473 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12473) / 12473 -
        finiteEnergy 12473 12473 (11 / 1000) / √12473 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12473 θ ^ 2 / gPlus 12473 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12473)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12473 θ ^ 2 / gPlus 12473 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12473)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12473 θ ^ 2 / gPlus 12473 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12473 ^ 2 ≤
      kappa (meanLowerRoot 12473 θ ^ 2 / gPlus 12473) - 2 / (12473 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12473 *
      (kappa (meanLowerRoot 12473 θ ^ 2 / gPlus 12473) - 2 / (12473 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12473 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12473)
    linarith
  have ht : √(12 * gPlus 12473) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12473 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12473 12473 (11 / 1000) / √12473 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12473)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12473 (gMinus 12473) (gPlus 12473)
      (finiteEnergy 12473 12473 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12473) (hτ : 0 < (paperDesignP 12473).tau0 c) :
    eR c = (2 / (mA 12473 : ℝ)) *
      normSq (BstLean.Part150.bT 12473 12473 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12473).tau0 c)) /
      (2 / (12473 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12473).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12473).tau0 c))⁻¹ •
      BstLean.Part150.bT 12473 12473 (A1 c) (A2 c) c.1.2 ((paperDesignP 12473).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12473 : ℝ)) * normSq (bR c) / (2 / (12473 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12473}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12473) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12473).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12473 : ℝ) * (paperDesignP 12473).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12473 12473 c.1.2 ((paperDesignP 12473).tau0 c) :=
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

end BstLean.Part266.Row12473

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12474 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12474).real (BstLean.Part211.CentreSource 12474 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12474) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12474 160 (6 / 1000)
  have hj := jS_160_le (n := 12474) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12474 160 (6 / 1000) ^ 2 * 12474 /
      (((12474 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12474 160 (6 / 1000) ^ 2 * 12474 /
      (((12474 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12474 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12474 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12474) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12474 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row12474

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 12474) :=
  Ethm (paperCentres 12474) ∩ Ethp (paperCentres 12474)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 12474)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 12474)
  have h2 := ethp_charge (by norm_num : 1 ≤ 12474) (paperCentres 12474)
  have he : exp (-(45 / 10000 * (12474 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (12474 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 12474) :=
  (passEvent ∩ agentEv (paperDesignP 12474) (DirectionError 12474) ∩
    agentEv (paperDesignP 12474) (CentreSources 12474 12474)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 12474)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 12474) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 12474) hτ
  have hC := centreSources_ret_charge_row 12474 (paperDesignP 12474) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 12474)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 12474) (CentreSources 12474 12474)
  direction : analyticBase ⊆ agentEv (paperDesignP 12474) (DirectionError 12474)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 12474)) : Set (Ret 12474) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 12474)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 12474)}
    (hT : (retDist (paperCentres 12474)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 12474)).real (H ∩ (baseEvent T)ᶜ) ≤
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

structure BaseEventCertificate (H T : Set (Ret 12474)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 12474)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 12474)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 12474)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row12474

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 12474 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √12474 := le_sqrt_of_sq_le (by norm_num)
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

theorem deltaChi_upper : BstLean.Part154.deltaChi 12474 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 12474 12474 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 12474)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 12474)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 12474
  have hb0 := BstLean.Part150.betaJ_nonneg 12474
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 12474 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 12474 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 12474 * BstLean.Part150.betaJ 12474) * 12474) ≤
      (79408387 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 12474)) * 12474 := by gcongr <;> linarith
      _ ≤ ((79408387 / 500000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 12474 * 12474 *
      (1 + BstLean.Part154.deltaChi 12474 12 + 2 / π) / BstLean.Part154.csC) ≤
      (181785053 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 12474 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((181785053 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((12474 : ℝ) / BstLean.Part154.csC) ≤ (98137 / 1000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (12474 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((98137 / 1000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 12474 : ℝ) * (79408387 / 500000) +
        2 * (1792 / 10000 / 12474) * (181785053 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (98137 / 1000) *
          (81 / 1000 / 12474 + (1792 / 10000 / 12474) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row12474

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row12474
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

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 12474 ∧
    1 ≤ gPlus 12474 ∧ gPlus 12474 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12474 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (12474 : ℝ) < √(1 - 2 / (12474 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (12474 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 12474 (gMinus 12474) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (12474 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 12474 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 12474 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 12474)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 12474 (gMinus 12474) (gPlus 12474)
      (finiteEnergy 12474 12474 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 12474 (gMinus 12474) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 12474 (gMinus 12474) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 12474 (gMinus 12474) (54 / 100))
    (by linarith : energyRatio 12474 (gMinus 12474) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 12474 (gMinus 12474) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 12474 * kappa (energyRatio 12474 (gMinus 12474) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 12474) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12474 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12474 12474 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 12474 12474 (11 / 1000) / √12474 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12474)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 12474 * kappa (energyRatio 12474 (gMinus 12474) (54 / 100))) +
      2 * √(12 * gPlus 12474) / 12474 + finiteEnergy 12474 12474 (11 / 1000) / √12474 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 12474 θ ∧ meanLowerRoot 12474 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 12474 - 2 / (12474 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 12474 - 2 / (12474 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 12474 θ ^ 2 / gPlus 12474) - 2 / (12474 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 12474 * (kappa (meanLowerRoot 12474 θ ^ 2 / gPlus 12474) -
        2 / (12474 : ℝ) ^ 2)) - 2 * √(12 * gPlus 12474) / 12474 -
        finiteEnergy 12474 12474 (11 / 1000) / √12474 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 12474 θ ^ 2 / gPlus 12474 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12474)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 12474 θ ^ 2 / gPlus 12474 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 12474)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 12474 θ ^ 2 / gPlus 12474 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 12474 ^ 2 ≤
      kappa (meanLowerRoot 12474 θ ^ 2 / gPlus 12474) - 2 / (12474 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 12474 *
      (kappa (meanLowerRoot 12474 θ ^ 2 / gPlus 12474) - 2 / (12474 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 12474 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 12474)
    linarith
  have ht : √(12 * gPlus 12474) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √12474 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 12474 12474 (11 / 1000) / √12474 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √12474)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 12474 (gMinus 12474) (gPlus 12474)
      (finiteEnergy 12474 12474 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 12474) (hτ : 0 < (paperDesignP 12474).tau0 c) :
    eR c = (2 / (mA 12474 : ℝ)) *
      normSq (BstLean.Part150.bT 12474 12474 (A1 c) (A2 c) c.1.2
        ((paperDesignP 12474).tau0 c)) /
      (2 / (12474 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 12474).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 12474).tau0 c))⁻¹ •
      BstLean.Part150.bT 12474 12474 (A1 c) (A2 c) c.1.2 ((paperDesignP 12474).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 12474 : ℝ)) * normSq (bR c) / (2 / (12474 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 12474}
    (hw : BstLean.Part161.WINDOW (paperDesignP 12474) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12474).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (12474 : ℝ) * (paperDesignP 12474).tau0 c ^ 2 :=
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
  have hE : (A1 c, A2 c) ∈ EnergySource 12474 12474 c.1.2 ((paperDesignP 12474).tau0 c) :=
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

end BstLean.Part266.Row12474
