import BstLean.Part262ActualInterface
import BstLean.Part273Row

/-! Part 275 (plan part L1), step 2: the analytic source charge from `8000 ≤ n`.
The charge is an explicit function of `n`: `sourceChargeFn n = 496145e-9 + centreCharge n`,
with `centreCharge n = 7989e-8 + 3445 / n²`. The only dimension-sensitive term is the
centre-source term. `jS_160_le` (from 8192) is replaced by `Part273.jS_le_jBound` at base 8000.
The table event has its two thresholds as parameters. -/
namespace BstLean.Part275
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part159
open BstLean.Part160 BstLean.Part161 BstLean.Part169 BstLean.Part212
open BstLean.Part252 BstLean.Part262

theorem exp_half_charge_8000 {n : ℕ} (hn : 8000 ≤ n) :
    exp (-(n : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h : exp (-(n : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    linarith
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem rhoBar_lt_8000 {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.Part154.rhoBar n BstLean.Part154.csC < 1 / 4 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (89 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hw : BstLean.Part153.wn n ≤ 2 := by
    unfold BstLean.Part153.wn
    have h1 : 2 / √(n : ℝ) ≤ 2 / 89 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have h0 : 0 ≤ 2 / √(n : ℝ) := by positivity
    nlinarith
  have hw0 : 0 ≤ BstLean.Part153.wn n := by unfold BstLean.Part153.wn; positivity
  have hpi : 1 / π ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) pi_gt_three.le
  have hc : 1 ≤ BstLean.Part154.csC := by unfold BstLean.Part154.csC; nlinarith
  unfold BstLean.Part154.rhoBar
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- The centre-source charge as an explicit function of `n`. -/
noncomputable def centreCharge (n : ℕ) : ℝ := 7989 / 10 ^ 8 + 3445 / (n : ℝ) ^ 2

theorem centreSources_charge_8000 {n : ℕ} (hn : 8000 ≤ n) (J : ℕ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (BstLean.Part211.CentreSource n J c τ 2)ᶜ ≤ centreCharge n := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hd : 0 < ((n : ℝ) - 1 - 2 * 160) * 2 := by linarith
  have hh := BstLean.Part211.centre_source_charge (n := n) (J := J) (P := 160)
    (η := 6 / 1000) (by omega) (by norm_num) (by omega) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt_8000 hn)
  have hj0 := jS_nonneg n 160 (6 / 1000)
  have hj := (BstLean.Part273.jS_le_jBound (le_refl 8000) hn).trans
    BstLean.Part273.jBound_8000_le
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
  have he := exp_half_charge_8000 hn
  have ht := exp_neg12_row
  unfold centreCharge
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_8000 {n : ℕ} (hn : 8000 ≤ n) (J : ℕ)
    (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources n J))ᶜ ≤ centreCharge n := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by omega) J)
    (by unfold centreCharge; positivity)
  intro c τ hτ
  exact centreSources_charge_8000 hn J c hτ

theorem passEvent_charge_8000 {n : ℕ} (hn : 8000 ≤ n) :
    (retDist (paperCentres n)).real (BstLean.Part262.passEvent n)ᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := n) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by omega) (paperDesignP n) hτ
  have hL := fresh_retained_charge160 (n := n) (q := 4)
    (by omega) (by norm_num) (paperDesignP n) hτ
  have h1 := (firstMatrix_charge (by omega) (paperDesignP n) hτ).trans (exp_half_charge_8000 hn)
  have h2 : (retDist (paperCentres n)).real (BstLean.Part164.Eop2 n)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
    refine (BstLean.Part164.Eop2_charge (by omega) (paperCentres n)).trans ?_
    have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
    rw [he, exp_add]
    exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
      (exp_pos _).le (by norm_num)).trans (by norm_num)
  have hC := (outputCentreEvent_charge (by omega : 1 ≤ n) (paperCentres n)).trans exp_neg12_row
  unfold BstLean.Part262.passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem worldAngles_charge_8000 {n : ℕ} (hn : 8000 ≤ n) :
    (retDist (paperCentres n)).real (BstLean.Part262.worldAngles n)ᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := ethm_charge (paperCentres n)
  have h2 := ethp_charge (by omega : 1 ≤ n) (paperCentres n)
  have he : exp (-(45 / 10000 * (n : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (n : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      linarith
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold BstLean.Part262.worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

/-- The analytic-base charge as an explicit function of `n`. -/
noncomputable def analyticChargeFn (n : ℕ) : ℝ := 446145 / 10 ^ 9 + centreCharge n

theorem analyticBase_charge_8000 {n : ℕ} (hn : 8000 ≤ n) :
    (retDist (paperCentres n)).real (BstLean.Part262.analyticBase n)ᶜ ≤ analyticChargeFn n := by
  have hτ := paperDesign_tauWorld (n := n) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by omega) (paperDesignP n) hτ
  have hC := centreSources_ret_charge_8000 hn n (paperDesignP n) hτ
  unfold BstLean.Part262.analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add (passEvent_charge_8000 hn) hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  refine ((measureReal_union_le _ _).trans (add_le_add hc (worldAngles_charge_8000 hn))).trans ?_
  unfold analyticChargeFn
  norm_num
  linarith

/-- The paid source charge (analytic base, positive output and `Operator160`) as a function
of `n`. -/
noncomputable def sourceChargeFn (n : ℕ) : ℝ := 496145 / 10 ^ 9 + centreCharge n

theorem paidSourceBase_charge_8000 {n : ℕ} (hn : 8000 ≤ n) (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (BstLean.Part262.paidSourceBase n)ᶜ) ≤ sourceChargeFn n := by
  have hs : H ∩ (BstLean.Part262.paidSourceBase n)ᶜ ⊆
      (BstLean.Part262.analyticBase n)ᶜ ∪ (positiveOutputEvent (paperCentres n))ᶜ ∪
        (agentEv (paperDesignP n) (Operator160 n))ᶜ := by
    intro c hc
    by_cases ha : c ∈ BstLean.Part262.analyticBase n
    · by_cases hp : c ∈ positiveOutputEvent (paperCentres n)
      · exact Or.inr (fun ho => hc.2 ⟨⟨ha, hp⟩, ho⟩)
      · exact Or.inl (Or.inr hp)
    · exact Or.inl (Or.inl ha)
  have hp := positiveOutputEvent_charge (by omega : 1 ≤ n) (paperCentres n)
  have ho := operator160_ret_charge (by omega) (paperDesignP n)
    (paperDesign_tauWorld _ _ _ _)
  refine ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans
        (add_le_add (analyticBase_charge_8000 hn) hp)) ho))).trans ?_
  unfold sourceChargeFn analyticChargeFn
  linarith

/-! ### The table event with parameter thresholds -/

/-- The exact-table event with thresholds `a ^ 8` (location) and `b ^ 8` (energy). -/
def tableEventP (n : ℕ) (a b : ℝ) : Set (Ret n) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ a ^ 8 ∧ BstLean.Part170.intW c ≤ b ^ 8}

theorem tableEventP_measurable (n : ℕ) (a b : ℝ) : MeasurableSet (tableEventP n a b) := by
  have hw : MeasurableSet {c : Ret n | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := n) measurable_id)
    (measurable_const (a := a ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := n) measurable_id)
    (measurable_const (a := b ^ 8))
  have heq : tableEventP n a b = {c : Ret n | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret n | BstLean.Part170.intF c ≤ a ^ 8} ∩
        {c : Ret n | BstLean.Part170.intW c ≤ b ^ 8}) := by
    ext c
    simp only [tableEventP, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem tableEventP_part262 (n : ℕ) :
    tableEventP n (649 / 10000) (2173 / 10000) = BstLean.Part262.tableEvent n := rfl

/-- The HQ base event with parameter table thresholds. -/
def hqBaseEventP (n : ℕ) (a b : ℝ) : Set (Ret n) :=
  (BstLean.Part262.analyticBase n ∩ tableEventP n a b) ∩ positiveOutputEvent (paperCentres n)

/-- The source base event with parameter table thresholds. -/
def sourceBaseP (n : ℕ) (a b : ℝ) : Set (Ret n) :=
  hqBaseEventP n a b ∩ agentEv (paperDesignP n) (Operator160 n)

theorem sourceBaseP_part262 (n : ℕ) :
    sourceBaseP n (649 / 10000) (2173 / 10000) = BstLean.Part262.sourceBase n := rfl

theorem sourceBaseP_measurable {n : ℕ} (hn : 1 ≤ n) (a b : ℝ) :
    MeasurableSet (sourceBaseP n a b) :=
  (((BstLean.Part262.analyticBase_measurable hn).inter (tableEventP_measurable n a b)).inter
    (positiveOutputEvent_measurable _)).inter
    (measurableSet_agentEv _ (measurableSet_Operator160 _))

theorem sourceBaseP_eq (n : ℕ) (a b : ℝ) :
    sourceBaseP n a b = BstLean.Part262.paidSourceBase n ∩ tableEventP n a b := by
  ext c
  simp only [sourceBaseP, hqBaseEventP, BstLean.Part262.paidSourceBase, mem_inter_iff]
  tauto

theorem sourceBaseP_charge {n : ℕ} (hn : 8000 ≤ n) {a b tb : ℝ}
    (hTable : (retDist (paperCentres n)).real (tableEventP n a b)ᶜ ≤ tb)
    (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (sourceBaseP n a b)ᶜ) ≤ sourceChargeFn n + tb := by
  have hs : H ∩ (sourceBaseP n a b)ᶜ ⊆ (H ∩ (BstLean.Part262.paidSourceBase n)ᶜ) ∪ (tableEventP n a b)ᶜ := by
    intro c hc
    rw [sourceBaseP_eq] at hc
    by_cases hp : c ∈ BstLean.Part262.paidSourceBase n
    · exact Or.inr (fun ht => hc.2 ⟨hp, ht⟩)
    · exact Or.inl ⟨hc.1, hp⟩
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (paidSourceBase_charge_8000 hn H) hTable))

/-! ### Values of the charge function -/

theorem centreCharge_anti {n0 n : ℕ} (h0 : 1 ≤ n0) (hn : n0 ≤ n) :
    centreCharge n ≤ centreCharge n0 := by
  have h0R : (1 : ℝ) ≤ n0 := by exact_mod_cast h0
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  unfold centreCharge
  have hsq : (n0 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hnR 2
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3445) (by positivity) hsq
  linarith

theorem sourceChargeFn_anti {n0 n : ℕ} (h0 : 1 ≤ n0) (hn : n0 ≤ n) :
    sourceChargeFn n ≤ sourceChargeFn n0 := by
  unfold sourceChargeFn
  linarith [centreCharge_anti h0 hn]

/-- The Part262 value `599145e-9` holds from 12224 (one dimension below the Part262 floor). -/
theorem sourceChargeFn_le_part262 {n : ℕ} (hn : 12224 ≤ n) :
    sourceChargeFn n ≤ 599145 / 10 ^ 9 :=
  (sourceChargeFn_anti (by norm_num) hn).trans (by norm_num [sourceChargeFn, centreCharge])

/-- From 8000 the source charge is at most `630e-6` (true value at 8000: about `629.86e-6`). -/
theorem sourceChargeFn_le_8000 {n : ℕ} (hn : 8000 ≤ n) :
    sourceChargeFn n ≤ 630 / 10 ^ 6 :=
  (sourceChargeFn_anti (by norm_num) hn).trans (by norm_num [sourceChargeFn, centreCharge])

/-- From 12225 the centre charge is at most the Part262 value `103e-6`. -/
theorem centreCharge_le_part262 {n : ℕ} (hn : 12225 ≤ n) :
    centreCharge n ≤ 103 / 10 ^ 6 :=
  (centreCharge_anti (by norm_num) hn).trans (by norm_num [centreCharge])

theorem centreCharge_8000_value : centreCharge 8000 ≤ 13373 / 10 ^ 8 := by
  norm_num [centreCharge]

end BstLean.Part275
