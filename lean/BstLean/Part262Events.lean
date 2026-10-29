import BstLean.Part252All
import BstLean.Part259Family

/-! The original analytic source events, with a variable dimension.
The table event uses the original retained distribution and exact-rule errors. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part159
open BstLean.Part160 BstLean.Part161 BstLean.Part169 BstLean.Part212
open BstLean.Part252

theorem exp_half_charge {n : ℕ} (hn : 12225 ≤ n) :
    exp (-(n : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have h : exp (-(n : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    linarith
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem centreSources_charge {n : ℕ} (hn : 12225 ≤ n) (J : ℕ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (BstLean.Part211.CentreSource n J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hd : 0 < ((n : ℝ) - 1 - 2 * 160) * 2 := by linarith
  have hh := BstLean.Part211.centre_source_charge (n := n) (J := J) (P := 160)
    (η := 6 / 1000) (by omega) (by norm_num) (by omega) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (BstLean.Part154.rhoBar_lt (by omega))
  have hj0 := jS_nonneg n 160 (6 / 1000)
  have hj := jS_160_le (by omega : 8192 ≤ n)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS n 160 (6 / 1000) ^ 2 * n /
      (((n : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    rw [div_le_iff₀ hd]
    have h := mul_le_mul_of_nonneg_right hj2 hn0
    norm_num at h ⊢
    nlinarith
  have hp' : (jS n 160 (6 / 1000) ^ 2 * n /
      (((n : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hbase 160).trans (by norm_num)
  have hden : (12225 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hnR 2
  have hr : (3445 : ℝ) / (n : ℝ) ^ 2 ≤ 3445 / (12225 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
  have he := exp_half_charge hn
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  norm_num at hr
  linarith

theorem centreSources_ret_charge {n : ℕ} (hn : 12225 ≤ n) (J : ℕ)
    (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources n J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by omega) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge hn J c hτ

def passEvent (n : ℕ) : Set (Ret n) :=
  agentEv (paperDesignP n) (Energy32 n) ∩
  agentEv (paperDesignP n) (freshRetainedEvent160 n 4) ∩
  agentEv (paperDesignP n) (FirstMatrix n) ∩
  BstLean.Part164.Eop2 n ∩ outputCentreEvent (paperCentres n)

theorem passEvent_measurable (n : ℕ) : MeasurableSet (passEvent n) :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem passEvent_charge {n : ℕ} (hn : 12225 ≤ n) :
    (retDist (paperCentres n)).real (passEvent n)ᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := n) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by omega) (paperDesignP n) hτ
  have hL := fresh_retained_charge160 (n := n) (q := 4)
    (by omega) (by norm_num) (paperDesignP n) hτ
  have h1 := (firstMatrix_charge (by omega) (paperDesignP n) hτ).trans (exp_half_charge hn)
  have h2 : (retDist (paperCentres n)).real (BstLean.Part164.Eop2 n)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
    refine (BstLean.Part164.Eop2_charge (by omega) (paperCentres n)).trans ?_
    have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
    rw [he, exp_add]
    exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
      (exp_pos _).le (by norm_num)).trans (by norm_num)
  have hC := (outputCentreEvent_charge (by omega : 1 ≤ n) (paperCentres n)).trans exp_neg12_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

def worldAngles (n : ℕ) : Set (Ret n) := Ethm (paperCentres n) ∩ Ethp (paperCentres n)

theorem worldAngles_measurable (n : ℕ) : MeasurableSet (worldAngles n) :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge {n : ℕ} (hn : 12225 ≤ n) :
    (retDist (paperCentres n)).real (worldAngles n)ᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := ethm_charge (paperCentres n)
  have h2 := ethp_charge (by omega : 1 ≤ n) (paperCentres n)
  have he : exp (-(45 / 10000 * (n : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (n : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      linarith
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase (n : ℕ) : Set (Ret n) :=
  (passEvent n ∩ agentEv (paperDesignP n) (DirectionError n) ∩
    agentEv (paperDesignP n) (CentreSources n n)) ∩ worldAngles n

theorem analyticBase_measurable {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (analyticBase n) :=
  ((passEvent_measurable n |>.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources hn _))).inter
        (worldAngles_measurable n)

theorem analyticBase_charge {n : ℕ} (hn : 12225 ≤ n) :
    (retDist (paperCentres n)).real (analyticBase n)ᶜ ≤ (549145 / 10 ^ 9 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := n) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by omega) (paperDesignP n) hτ
  have hC := centreSources_ret_charge hn n (paperDesignP n) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add (passEvent_charge hn) hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc (worldAngles_charge hn))).trans
    (by norm_num)

def tableEvent (n : ℕ) : Set (Ret n) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable (n : ℕ) : MeasurableSet (tableEvent n) := by
  have hw : MeasurableSet {c : Ret n | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := n) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := n) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent n = {c : Ret n | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret n | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret n | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

def hqBaseEvent (n : ℕ) : Set (Ret n) :=
  (analyticBase n ∩ tableEvent n) ∩ positiveOutputEvent (paperCentres n)

def sourceBase (n : ℕ) : Set (Ret n) :=
  hqBaseEvent n ∩ agentEv (paperDesignP n) (Operator160 n)

theorem hqBaseEvent_measurable {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (hqBaseEvent n) :=
  ((analyticBase_measurable hn).inter (tableEvent_measurable n)).inter
    (positiveOutputEvent_measurable _)

theorem sourceBase_measurable {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (sourceBase n) :=
  (hqBaseEvent_measurable hn).inter (measurableSet_agentEv _ (measurableSet_Operator160 _))

theorem hqBaseEvent_charge {n : ℕ} (hn : 12225 ≤ n) {b : ℝ}
    (hTable : (retDist (paperCentres n)).real (tableEvent n)ᶜ ≤ b)
    (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (hqBaseEvent n)ᶜ) ≤ 549145 / 10 ^ 9 + b := by
  have hs : H ∩ (hqBaseEvent n)ᶜ ⊆
      (analyticBase n)ᶜ ∪ (tableEvent n)ᶜ ∪
        (positiveOutputEvent (paperCentres n))ᶜ := by
    intro c hc
    by_cases ha : c ∈ analyticBase n
    · by_cases ht : c ∈ tableEvent n
      · exact Or.inr (fun hp => hc.2 ⟨⟨ha, ht⟩, hp⟩)
      · exact Or.inl (Or.inr ht)
    · exact Or.inl (Or.inl ha)
  have hp := positiveOutputEvent_charge (by omega : 1 ≤ n) (paperCentres n)
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans
        (add_le_add (analyticBase_charge hn) hTable)) hp))).trans (by simp)

theorem sourceBase_charge {n : ℕ} (hn : 12225 ≤ n) {b : ℝ}
    (hTable : (retDist (paperCentres n)).real (tableEvent n)ᶜ ≤ b)
    (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (sourceBase n)ᶜ) ≤
      599145 / 10 ^ 9 + b := by
  have hs : H ∩ (sourceBase n)ᶜ ⊆ (H ∩ (hqBaseEvent n)ᶜ) ∪
      (agentEv (paperDesignP n) (Operator160 n))ᶜ := by
    intro c hc
    by_cases hb : c ∈ hqBaseEvent n
    · exact Or.inr (fun ho => hc.2 ⟨hb, ho⟩)
    · exact Or.inl ⟨hc.1, hb⟩
  have hp := operator160_ret_charge (by omega) (paperDesignP n)
    (paperDesign_tauWorld _ _ _ _)
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (hqBaseEvent_charge hn hTable H) hp))).trans (by linarith)

def paidSourceBase (n : ℕ) : Set (Ret n) :=
  (analyticBase n ∩ positiveOutputEvent (paperCentres n)) ∩
    agentEv (paperDesignP n) (Operator160 n)

theorem paidSourceBase_measurable {n : ℕ} (hn : 1 ≤ n) :
    MeasurableSet (paidSourceBase n) :=
  ((analyticBase_measurable hn).inter (positiveOutputEvent_measurable _)).inter
    (measurableSet_agentEv _ (measurableSet_Operator160 _))

theorem paidSourceBase_charge {n : ℕ} (hn : 12225 ≤ n) (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (paidSourceBase n)ᶜ) ≤
      (599145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ (paidSourceBase n)ᶜ ⊆
      (analyticBase n)ᶜ ∪ (positiveOutputEvent (paperCentres n))ᶜ ∪
        (agentEv (paperDesignP n) (Operator160 n))ᶜ := by
    intro c hc
    by_cases ha : c ∈ analyticBase n
    · by_cases hp : c ∈ positiveOutputEvent (paperCentres n)
      · exact Or.inr (fun ho => hc.2 ⟨⟨ha, hp⟩, ho⟩)
      · exact Or.inl (Or.inr hp)
    · exact Or.inl (Or.inl ha)
  have hp := positiveOutputEvent_charge (by omega : 1 ≤ n) (paperCentres n)
  have ho := operator160_ret_charge (by omega) (paperDesignP n)
    (paperDesign_tauWorld _ _ _ _)
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans
        (add_le_add (analyticBase_charge hn) hp)) ho))).trans (by linarith)

theorem sourceBase_eq (n : ℕ) : sourceBase n = paidSourceBase n ∩ tableEvent n := by
  ext c
  simp only [sourceBase, hqBaseEvent, paidSourceBase, mem_inter_iff]
  tauto

structure SourceEvents {n : ℕ} (c : Ret n) : Prop where
  world_centre_pos : 0 < normSq c.1.2
  scale_pos : 0 < (paperDesignP n).tau0 c
  base_event : c.2.1.1 ∈ BstLean.Part222.centreBase n n c.1.2 ((paperDesignP n).tau0 c)
  error_event : c.2.1.1 ∈ BstLean.Part215.sharpErrorEvent c.1.2 ((paperDesignP n).tau0 c)
  operator_event : c.2.1.1 ∈ BstLean.Part215.operatorEvent c.1.2
    ((paperDesignP n).tau0 c) 0.006 (ENNReal.ofReal (1 / 20000))
  energy_event : c.2.1.1 ∈ BstLean.Part222.energyEvent c.1.2 ((paperDesignP n).tau0 c)

theorem sourceEvents_of_base {n : ℕ} {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (hc : c ∈ sourceBase n) : SourceEvents c := by
  have ha := hc.1.1.1
  have hn : 0 < normSq c.1.2 :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm fun h => hw.1 (normSq_eq_zero h))
  refine ⟨hn, hw.2.1, ?_, ?_, ?_, ?_⟩
  · exact ⟨2, by norm_num, ha.1.2 hw.2.1⟩
  · exact ha.1.1.2 hw.2.1
  · have he : (6 / 1000 : ℝ) = 0.006 := by norm_num
    rw [← he]
    exact hc.2 hw.2.1
  · exact ha.1.1.1.1.1.1.1 hw.2.1

end BstLean.Part262
