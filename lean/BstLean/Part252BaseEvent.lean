import BstLean.Part252PassEvent
import BstLean.Part252DirectionEvent
import BstLean.Part252CentreCharge
import BstLean.Part252OperatorEvent
import BstLean.Part249Ledger

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part252
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

end BstLean.Part252
