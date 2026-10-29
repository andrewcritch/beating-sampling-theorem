import BstLean.Part160Defs
import BstLean.Part157All

/-!
# Part 160 (file `Event`): the Agent-stage event as an event of the retained data

Do not use `sorry`, `native_decide` or `axiom`.

* `retDist_agent_charge`: a family of events of `(A₁, A₂)` indexed by `(ĉ, τ₀)`, each with
  complement probability at most `δ` when `τ₀ > 0`, gives an event of the retained data with
  complement probability at most `δ` (the matrices `(A₁, A₂)` are independent of the retained
  World data; `τ₀` is a function of the retained World data).
* `agentEv D S`, `measurableSet_agentEv`, `events_with_agent`: `EVENTS_hyp` with the event added
  to `E₁` and the charge added to `δ_extra`.
* `EA16 D`: the event `GoodC16` of Part 154 at `(ĉ, τ₀)`; `measurableSet_EA16`, `EA16_charge`,
  `EA16_charge_num` (`≤ 15/100000`), `events_with_EA16`.
* `paperDesign_agentCentre`, `paperDesign_tauWorld`: the design of the paper has the Agent centre
  of Part 154 and a `τ₀` that is a function of the retained World data.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part150 (rhoC thetaC bT)
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- The index type of a family of Agent events: `((ĉ, τ₀), (A₁, A₂))`. -/
abbrev AgFam (n : ℕ) : Type :=
  ((Fin n → ℝ) × ℝ) × (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

/-- The map `c ↦ ((ĉ, τ₀), (A₁, A₂))` of the retained data. -/
noncomputable def agKey (D : Design n) (c : Ret n) : AgFam n := ((c.1.2, D.tau0 c), c.2.1.1)

lemma measurable_agKey (D : Design n) : Measurable (agKey D) :=
  ((measurable_snd.comp measurable_fst).prodMk D.mtau0).prodMk
    (measurable_fst.comp (measurable_fst.comp measurable_snd))

/-- The retained-data event of a family `S`: if `τ₀ > 0` then `((ĉ, τ₀), (A₁, A₂)) ∈ S`. -/
def agentEv (D : Design n) (S : Set (AgFam n)) : Set (Ret n) :=
  {c | 0 < D.tau0 c → agKey D c ∈ S}

lemma measurableSet_agentEv (D : Design n) {S : Set (AgFam n)} (hS : MeasurableSet S) :
    MeasurableSet (agentEv D S) := by
  have h1 : MeasurableSet {c : Ret n | 0 < D.tau0 c} := measurableSet_lt measurable_const D.mtau0
  have h2 : MeasurableSet {c : Ret n | agKey D c ∈ S} := (measurable_agKey D) hS
  have e : agentEv D S = {c : Ret n | 0 < D.tau0 c}ᶜ ∪ {c : Ret n | agKey D c ∈ S} := by
    ext c
    simp only [agentEv, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  rw [e]
  exact h1.compl.union h2

lemma agentEv_compl (D : Design n) (S : Set (AgFam n)) :
    (agentEv D S)ᶜ = {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S} := by
  ext c
  simp only [agentEv, agKey, Set.mem_compl_iff, Set.mem_ofPred_eq]
  tauto

/-- The Agent hidden matrices under the noise of `(Agent retained data, F)`. -/
lemma map_agentHid :
    ((cAm n).prod (mlpGauss n (mF n) 1)).map (fun y : ARet n × FPar n => y.1.1) =
      hidGauss n (mA n) := by
  have e : (fun y : ARet n × FPar n => y.1.1) = Prod.fst ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map measurable_fst measurable_fst]
  unfold cAm
  rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul]

/-- **The charge of a family of Agent events under the distribution of the retained data.** -/
theorem retDist_agent_charge (D : Design n) (hτ : TauWorld D) {S : Set (AgFam n)}
    (hS : MeasurableSet S) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ → (nuA n).real {θ | ((c, τ), θ) ∉ S} ≤ δ) :
    (retDist D.toCentres).real
      {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S} ≤ δ := by
  obtain ⟨τW, hτm, hτe⟩ := hτ
  have hT : MeasurableSet {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S} := by
    rw [← agentEv_compl]
    exact (measurableSet_agentEv D hS).compl
  have mr := measurable_retVal D.toCentres
  rw [← noise_retVal D.toCentres, map_measureReal_apply mr hT]
  have hP := mr hT
  have key : (noiseC n) (retVal D.toCentres ⁻¹'
      {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S}) ≤ ENNReal.ofReal δ := by
    unfold noiseC
    rw [Measure.prod_apply hP]
    have hb : ∀ w : WRet n, ((cAm n).prod (mlpGauss n (mF n) 1))
        (Prod.mk w ⁻¹' (retVal D.toCentres ⁻¹'
          {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S})) ≤ ENNReal.ofReal δ := by
      intro w
      by_cases hpos : 0 < τW (retValW D.toCentres w)
      · have hB : MeasurableSet {θ : AHid n |
            (((retValW D.toCentres w).2, τW (retValW D.toCentres w)), θ) ∉ S} :=
          (measurable_prodMk_left hS).compl
        have e : (Prod.mk w ⁻¹' (retVal D.toCentres ⁻¹'
            {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S})) =
            (fun y : ARet n × FPar n => y.1.1) ⁻¹' {θ : AHid n |
              (((retValW D.toCentres w).2, τW (retValW D.toCentres w)), θ) ∉ S} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, hτe]
          show (0 < τW (retValW D.toCentres w) ∧ _) ↔ _
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨hpos, h⟩
        have h0 : ((cAm n).prod (mlpGauss n (mF n) 1))
            ((fun y : ARet n × FPar n => y.1.1) ⁻¹' {θ : AHid n |
              (((retValW D.toCentres w).2, τW (retValW D.toCentres w)), θ) ∉ S}) =
            (hidGauss n (mA n)) {θ : AHid n |
              (((retValW D.toCentres w).2, τW (retValW D.toCentres w)), θ) ∉ S} := by
          rw [← map_agentHid]
          exact (Measure.map_apply (show Measurable (fun y : ARet n × FPar n => y.1.1) from
            measurable_fst.comp measurable_fst) hB).symm
        rw [e, h0]
        have h := hδ (retValW D.toCentres w).2 (τW (retValW D.toCentres w)) hpos
        have h2 : (hidGauss n (mA n)) {θ : AHid n |
            (((retValW D.toCentres w).2, τW (retValW D.toCentres w)), θ) ∉ S} =
            ENNReal.ofReal ((nuA n).real {θ |
              (((retValW D.toCentres w).2, τW (retValW D.toCentres w)), θ) ∉ S}) := by
          exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        rw [h2]
        exact ENNReal.ofReal_le_ofReal h
      · have e : (Prod.mk w ⁻¹' (retVal D.toCentres ⁻¹'
            {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S})) = ∅ := by
          ext y
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, hτe, Set.mem_empty_iff_false, iff_false]
          intro h
          exact hpos h.1
        rw [e, measure_empty]
        exact bot_le
    calc ∫⁻ w, ((cAm n).prod (mlpGauss n (mF n) 1))
          (Prod.mk w ⁻¹' (retVal D.toCentres ⁻¹'
            {c : Ret n | 0 < D.tau0 c ∧ ((c.1.2, D.tau0 c), c.2.1.1) ∉ S})) ∂cWm n
        ≤ ∫⁻ _w, ENNReal.ofReal δ ∂cWm n := lintegral_mono hb
      _ = ENNReal.ofReal δ := by rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal hδ0 key

/-- **`EVENTS_hyp` with one more family of Agent events**: the event is added to `E₁`, and its
charge `δ'` to `δ_extra`. -/
theorem events_with_agent (D : Design n) (hτ : TauWorld D) {S : Set (AgFam n)}
    (hS : MeasurableSet S) {δ' : ℝ} (hδ0 : 0 ≤ δ')
    (hδ : ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ → (nuA n).real {θ | ((c, τ), θ) ∉ S} ≤ δ')
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhid vW δextra) :
    EVENTS_hyp D.toCentres H (E₁ ∩ agentEv D S) Hbar δhid vW (δextra + δ') := by
  obtain ⟨hH, hE₁, hHm, hhid, hHint, hvW, hextra⟩ := hEv
  refine ⟨hH, hE₁.inter (measurableSet_agentEv D hS), hHm, hhid, hHint, hvW, ?_⟩
  have hsub : H ∩ (E₁ ∩ agentEv D S)ᶜ ⊆ (H ∩ E₁ᶜ) ∪ (agentEv D S)ᶜ := by
    intro c hc
    by_cases h1 : c ∈ E₁
    · exact Or.inr fun h2 => hc.2 ⟨h1, h2⟩
    · exact Or.inl ⟨hc.1, h1⟩
  have h1 := measureReal_mono (μ := retDist D.toCentres) hsub
  have h2 := measureReal_union_le (μ := retDist D.toCentres) (H ∩ E₁ᶜ) (agentEv D S)ᶜ
  have h3 := retDist_agent_charge D hτ hS hδ0 hδ
  rw [← agentEv_compl] at h3
  linarith

lemma goodSet_inter_subset (H E₁ E₂ : Set (Ret n)) (Hbar : Ret n → ℝ) (hW : ℝ) :
    goodSet H (E₁ ∩ E₂) Hbar hW ⊆ goodSet H E₁ Hbar hW :=
  fun _ hc => ⟨hc.1, hc.2.1⟩

lemma goodSet_inter_mem {H E₁ E₂ : Set (Ret n)} {Hbar : Ret n → ℝ} {hW : ℝ} {c : Ret n}
    (hc : c ∈ goodSet H (E₁ ∩ E₂) Hbar hW) : c ∈ E₂ := hc.2.2

/-! ## The event `GoodC16` of Part 154 -/

/-- **The Agent event of Part 154 as an event of the retained data**: if `τ₀ > 0`, then
`(A₁, A₂) ∈ GoodC16 n n ĉ τ₀`. -/
def EA16 (D : Design n) : Set (Ret n) :=
  {c | 0 < D.tau0 c → (c.2.1.1.1, c.2.1.1.2) ∈ BstLean.Part154.GoodC16 n n c.1.2 (D.tau0 c)}

lemma EA16_eq (D : Design n) : EA16 D = agentEv D (BstLean.Part154.SC16 n) := rfl

theorem measurableSet_EA16 (hn : 1 ≤ n) (D : Design n) : MeasurableSet (EA16 D) := by
  rw [EA16_eq]
  exact measurableSet_agentEv D (BstLean.Part154.measurableSet_SC16 hn)

lemma charge16_nonneg (n : ℕ) :
    0 ≤ rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 := by
  positivity

lemma SC16_charge (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ BstLean.Part154.SC16 n} ≤
      rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 :=
  BstLean.Part154.GoodC16_prob hn n c hτ

/-- **The charge of the Agent event**: `Pr((EA16 D)ᶜ) ≤ e^{−n/2} + 13e^{−12} + 3445/n² + 5·10⁻⁵`
under the distribution of the retained data, `n ≥ 16 384`. -/
theorem EA16_charge (hn : 16384 ≤ n) (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (EA16 D)ᶜ ≤
      rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 := by
  rw [EA16_eq, agentEv_compl]
  exact retDist_agent_charge D hτ (BstLean.Part154.measurableSet_SC16 (by omega))
    (charge16_nonneg n) (SC16_charge hn)

lemma exp_neg_twelve_le : rexp (-12) ≤ 615 / 10 ^ 8 := by
  have h1 : (2.7182818283 : ℝ) < rexp 1 := Real.exp_one_gt_d9
  have h2 : rexp 12 = rexp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (2.7182818283 : ℝ) ^ 12 ≤ rexp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h1.le 12
  have h4 : (10 ^ 8 / 615 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
  rw [show (-12 : ℝ) = -(12 : ℝ) by norm_num, Real.exp_neg, h2]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  have e : (615 / 10 ^ 8 : ℝ)⁻¹ = 10 ^ 8 / 615 := by norm_num
  rw [e]
  linarith

lemma charge16_le (hn : 16384 ≤ n) :
    rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 ≤ 15 / 100000 := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : rexp (-(n : ℝ) / 2) ≤ rexp (-12) := Real.exp_le_exp.mpr (by linarith)
  have h2 := exp_neg_twelve_le
  have h3 : 3445 / (n : ℝ) ^ 2 ≤ 3445 / (16384 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hnR 2)
  have h4 : (3445 : ℝ) / 16384 ^ 2 ≤ 1284 / 10 ^ 8 := by norm_num
  linarith

/-- `Pr((EA16 D)ᶜ) ≤ 15/100000`, `n ≥ 16 384`. -/
theorem EA16_charge_num (hn : 16384 ≤ n) (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (EA16 D)ᶜ ≤ 15 / 100000 :=
  (EA16_charge hn D hτ).trans (charge16_le hn)

/-- **`EVENTS_hyp` with the Agent event of Part 154**: `E₁` becomes `E₁ ∩ EA16 D`, and
`δ_extra` becomes `δ_extra + 15/100000`. -/
theorem events_with_EA16 (hn : 16384 ≤ n) (D : Design n) (hτ : TauWorld D)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhid vW δextra) :
    EVENTS_hyp D.toCentres H (E₁ ∩ EA16 D) Hbar δhid vW (δextra + 15 / 100000) := by
  rw [EA16_eq]
  exact events_with_agent D hτ (BstLean.Part154.measurableSet_SC16 (by omega)) (by norm_num)
    (fun c τ h => (SC16_charge hn c τ h).trans (charge16_le hn)) hEv

lemma goodSet_EA16_subset (D : Design n) (H E₁ : Set (Ret n)) (Hbar : Ret n → ℝ) (hW : ℝ) :
    goodSet H (E₁ ∩ EA16 D) Hbar hW ⊆ goodSet H E₁ Hbar hW :=
  goodSet_inter_subset H E₁ (EA16 D) Hbar hW

lemma goodSet_EA16_mem (D : Design n) {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {hW : ℝ} :
    ∀ c ∈ goodSet H (E₁ ∩ EA16 D) Hbar hW, c ∈ EA16 D := fun _ hc => hc.2.2

/-! ## The design of the paper -/

theorem paperDesign_agentCentre (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    AgentCentre154 (paperDesign n fT wT hf hw) := by
  intro c
  funext j
  show bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (tau0p c.1.1) j / rhoC c.1.2 (tau0p c.1.1) =
    1 / rhoC c.1.2 (tau0p c.1.1) * bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (tau0p c.1.1) j
  ring

theorem paperDesign_tauWorld (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    TauWorld (paperDesign n fT wT hf hw) :=
  ⟨fun w => tau0p w.1, measurable_tau0p.comp measurable_fst, fun _ => rfl⟩

end BstLean.Part160

open BstLean.Part160 in
#print axioms retDist_agent_charge
open BstLean.Part160 in
#print axioms events_with_agent
open BstLean.Part160 in
#print axioms measurableSet_EA16
open BstLean.Part160 in
#print axioms EA16_charge
open BstLean.Part160 in
#print axioms EA16_charge_num
open BstLean.Part160 in
#print axioms events_with_EA16
open BstLean.Part160 in
#print axioms paperDesign_agentCentre
open BstLean.Part160 in
#print axioms paperDesign_tauWorld
