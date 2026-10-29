import BstLean.Part160All
import BstLean.Part159All

/-!
# Part 163 (file `Comb`): the correct combination of Parts 159 and 160

Do not use `sorry`, `native_decide` or `axiom`.

Part 160's `classifier_paper_comb23` asks `REPLA_mix_hyp` on
`goodSet (HP n) (E_{θ−} ∩ E_{θ+}) (HbarW D) hWL`, a set defined by World data only; that hypothesis
cannot hold (Part 162, report §4.9; Part 163 report §4). This file repairs the combination.

* `Eframe D`: the seven Agent events on which Part 160 proves the Agent frame bound `3.05/n`
  (`EA16`, `SXi`, `SXi4n`, `SXi8n`, `SSc`, `SScU`, `SD'`); charge `≤ 33.515·10⁻⁵ ≤ 34·10⁻⁵`.
* `classifier_frame_free23`: Part 160's `classifier_agentframe5_23000` with the World frame bound,
  the window and the Agent replacement asked ONLY on `goodSet H (E₁ ∩ Eframe D)`; the frame events
  are charged once (inside the proof).
* `roomA`: the room left in the ledger for a free Agent event `E_A`;
  `3059/10⁶ ≤ roomA` (`roomA_ge`).
* **`classifier_paper_free23`**: for `paperDesign` and every `n ≥ 23 000`: IF `E_A` is a measurable
  event with `Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomA`, and `REPLA_mix_hyp` holds on
  `goodSet (HP n) (E_{θ−} ∩ E_{θ+} ∩ E_A ∩ Eframe D) (HbarW D) hWL`, THEN success `≥ 99/100`.
-/

namespace BstLean.Part163

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

variable {n : ℕ}

/-- **The Agent event of Part 160's frame bound**: the intersection of the seven Agent events
`EA16`, `SXi`, `SXi4n`, `SXi8n`, `SSc`, `SScU`, `SD'` (each as an event of the retained data). -/
def Eframe (D : Design n) : Set (Ret n) :=
  EA16 D ∩ agentEv D (SXi n) ∩ agentEv D (SXi4n n) ∩ agentEv D (SXi8n n) ∩ agentEv D (SSc n) ∩
    agentEv D (SScU n) ∩ agentEv D (SD' n)

theorem measurableSet_Eframe (hn : 1 ≤ n) (D : Design n) : MeasurableSet (Eframe D) :=
  ((((((measurableSet_EA16 hn D).inter (measurableSet_agentEv D (measurableSet_SXi n))).inter
    (measurableSet_agentEv D (measurableSet_SXi4n n))).inter
    (measurableSet_agentEv D (measurableSet_SXi8n n))).inter
    (measurableSet_agentEv D (measurableSet_SSc n))).inter
    (measurableSet_agentEv D (measurableSet_SScU n))).inter
    (measurableSet_agentEv D (measurableSet_SD' n))

lemma chain_eq (D : Design n) (E₁ : Set (Ret n)) :
    ((((((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩ agentEv D (SXi4n n)) ∩ agentEv D (SXi8n n)) ∩
      agentEv D (SSc n)) ∩ agentEv D (SScU n)) ∩ agentEv D (SD' n) = E₁ ∩ Eframe D := by
  ext c
  simp only [Eframe, Set.mem_inter_iff]
  tauto

/-- **`EVENTS_hyp` with the frame event**: `E₁` becomes `E₁ ∩ Eframe D` and `δ_extra` becomes
`δ_extra + 33515/10⁸` (`n ≥ 16 384`, `τ₀` a function of the World data). -/
theorem events_with_Eframe (hn : 16384 ≤ n) (D : Design n) (hτ : TauWorld D)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhid vW δextra) :
    EVENTS_hyp D.toCentres H (E₁ ∩ Eframe D) Hbar δhid vW (δextra + 33515 / 10 ^ 8) := by
  have hEv0 := events_with_EA16 hn D hτ hEv
  have hEv1 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (SXi_charge hn) hEv0
  have hEv2 := events_with_agent D hτ (measurableSet_SXi4n n) (by norm_num)
    (SXi4n_charge hn) hEv1
  have hEv3 := events_with_agent D hτ (measurableSet_SXi8n n) (by norm_num)
    (SXi8n_charge hn) hEv2
  have hEv4 := events_with_agent D hτ (measurableSet_SSc n) (by norm_num)
    (SSc_charge_num hn) hEv3
  have hEv5 := events_with_agent D hτ (measurableSet_SScU n) (by norm_num)
    (SScU_charge_num hn) hEv4
  have hEv6 := events_with_agent D hτ (measurableSet_SD' n) (by norm_num)
    (fun c τ _ => SD'_charge (by omega) c τ) hEv5
  rw [chain_eq] at hEv6
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hEv6
  exact ⟨h1, h2, h3, h4, h5, h6, by linarith⟩

/-- **Part 160's frame bound on the frame event**: `FRAME_A_hyp D (3.05/n)` on every subset of
`goodSet H (E₁ ∩ Eframe D)` where the window holds (`n ≥ 23 000`). -/
theorem frameA_on_Eframe (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    {H E₁ : Set (Ret n)} (hWin : WINDOW_hyp D (goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL)) :
    FRAME_A_hyp D (305 / 100 / n) (goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL) := by
  have hm : ∀ c ∈ goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL, c ∈ Eframe D := fun c hc => hc.2.2
  exact frameA5_23000 hn D hD hWin
    (fun c hc => (hm c hc).1.1.1.1.1.1)
    (fun c hc => (hm c hc).1.1.1.1.1.2)
    (fun c hc => (hm c hc).1.1.1.1.2)
    (fun c hc => (hm c hc).1.1.1.2)
    (fun c hc => (hm c hc).1.1.2)
    (fun c hc => (hm c hc).1.2)
    (fun c hc => (hm c hc).2)

/-- **The conditional classifier theorem with the frame event charged once (every `n ≥ 23 000`).**
IF `EVENTS_hyp` holds for `H`, `E₁` with `δ_hid + v_W/h_W² + δ_extra + 34·10⁻⁵ ≤ 0.0063`, and on
`goodSet H (E₁ ∩ Eframe D)` the window, the World frame bound and the Agent replacement hold, THEN
success `≥ 99/100`. The Agent frame bound is used only on `Eframe D`, and `Eframe D` is charged
once. -/
theorem classifier_frame_free23 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 34 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hEv' := events_with_Eframe (by omega) D hτ hEv
  exact classifier_frame_305 hn D t hEv' (by linarith) hFW (frameA_on_Eframe hn D hD hWin) hRA

/-! ## The paper's design -/

/-- **The room left in the ledger for a free Agent event**:
`0.0063 − δ_Pap − v_Pap/h_W² − δ_Ang − 34·10⁻⁵` (about `0.0030592`). -/
noncomputable def roomA : ℝ :=
  63 / 10 ^ 4 - BstLean.Part159.δPap - BstLean.Part159.vPap / hWL ^ 2 - BstLean.Part159.δAng -
    34 / 100000

theorem roomA_ge : (3059 : ℝ) / 10 ^ 6 ≤ roomA := by
  unfold roomA BstLean.Part159.δPap BstLean.Part159.vPap BstLean.Part159.δAng hWL
  norm_num

/-- **The classifier theorem for the paper's design with a free Agent event (every `n ≥ 23 000`).**
IF `E_A` is a measurable event of the retained data (a condition on the Agent and `F` data,
possibly with World data) with `Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A` and `δ_A ≤ roomA`
(`roomA ≥ 0.003059`), and the Agent replacement root `h_A` holds on
`HP n ∩ {H̄_W ≤ h_W} ∩ (E_{θ−} ∩ E_{θ+} ∩ E_A ∩ Eframe D)`, THEN the program succeeds with
probability at least `99/100`. The World stage is Part 159; the Agent frame bound `3.05/n` is
Part 160's, used only on its own event `Eframe D`, which is charged once (`34·10⁻⁵`). -/
theorem classifier_paper_free23 (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomA)
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  set D := paperDesign n fT wT hf hw with hDd
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA
    with hE₁d
  have hE₁ : MeasurableSet E₁ :=
    ((BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)).inter hEA
  obtain ⟨hW1, hW2⟩ := BstLean.Part159.paper_world hn16 D rfl (fun _ => rfl)
  have hch : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng + δA := by
    have h := BstLean.Part159.extra_angle hn16 (paperCentres n) (BstLean.Part159.HP n) EA
    exact h.trans (add_le_add le_rfl hA)
  have hEv := hW1 hE₁ hch
  have hWin : WINDOW_hyp D (goodSet (BstLean.Part159.HP n) (E₁ ∩ Eframe D) (HbarW D) hWL) :=
    window_paper hn16 fT wT hf hw (fun c hc => ⟨hc.1.1, hc.2.1.1.1, hc.2.1.1.2⟩)
  have hFW := hW2 (E := goodSet (BstLean.Part159.HP n) (E₁ ∩ Eframe D) (HbarW D) hWL)
    (fun c hc => hc.1.1)
  have hsum : BstLean.Part159.δPap + BstLean.Part159.vPap / hWL ^ 2 +
      (BstLean.Part159.δAng + δA) + 34 / 100000 ≤ 63 / 10 ^ 4 := by
    unfold roomA at hroom
    linarith
  exact classifier_frame_free23 hn D (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv hsum hWin hFW hRA

/-- The same with the explicit room: `δ_A ≤ 0.003059`. -/
theorem classifier_paper_free23' (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ 3059 / 10 ^ 6)
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_free23 hn fT wT hf hw t hEA hA (hroom.trans roomA_ge) hRA

end BstLean.Part163

open BstLean.Part163 in
#print axioms events_with_Eframe
open BstLean.Part163 in
#print axioms frameA_on_Eframe
open BstLean.Part163 in
#print axioms classifier_frame_free23
open BstLean.Part163 in
#print axioms roomA_ge
open BstLean.Part163 in
#print axioms classifier_paper_free23
open BstLean.Part163 in
#print axioms classifier_paper_free23'
