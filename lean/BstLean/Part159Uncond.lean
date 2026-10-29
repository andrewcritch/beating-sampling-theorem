import BstLean.Part159PaperW
import BstLean.Part159Kap

/-!
# Part 159 (file `Uncond`): the classifier theorem for the design of the paper's program with
ONLY Agent-side hypotheses, every `n ≥ 16 384`

Role: `delegations/statements/p159-spec.md`, items 2 and 3. Do not use `sorry`, `native_decide`
or `axiom`.

The two hypotheses `ConstC n`, `ConstK n` on the computed constants `c̃_N`, `κ̃` of the paper's
program are PROVED for every `n ≥ 16 384` (files `Pi`, `Kap`). So every World
hypothesis of the conditional classifier theorem holds for `paperDesign` with no hypothesis.

* `paper_world`: the World package for the paper's centre and scalar: hidden charge, frame bound,
  Hellinger moment, as `EVENTS_hyp` and `FRAME_W_hyp`.
* **`classifier_paper_agent`**: the conditional theorem for `paperDesign` with only Agent-side
  hypotheses.
* `classifier_paper_agent_window`: the same with the two angle events proved.
* `classifier_paper_agent_charges`: a free charge `δ_extra`: failure `≤ 0.0060527 + δ_extra`.
* `theta_window_paper'`: the retained World window with no hypothesis on the constants.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- **The World package for the centre and the scalar of the paper's program**
(every `n ≥ 16 384`), for every design with `b_W = bWp`, `τ₀ = tau0p`: `EVENTS_hyp` with the
hidden charge `0.00163204` and the Hellinger moment `7.37·10⁻⁹` (the charge of the other events is
a hypothesis), and `FRAME_W_hyp` with `1.377/n`. -/
theorem paper_world (hn : 16384 ≤ n) (D : Design n) (hD : D.bW = bWp)
    (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) :
    (∀ {E₁ : Set (Ret n)}, MeasurableSet E₁ → ∀ {δextra : ℝ},
      (retDist D.toCentres).real (HP n ∩ E₁ᶜ) ≤ δextra →
        EVENTS_hyp D.toCentres (HP n) E₁ (HbarW D) δPap vPap δextra) ∧
    (∀ {E : Set (Ret n)}, E ⊆ HP n → FRAME_W_hyp D.toCentres (cWL / n) E) :=
  ⟨fun hE₁ _ h3 => events_paper hn (constC (by omega)) (constK (by omega)) D hD hτ hE₁ h3,
    fun hE => frame_w_paper hn (constC (by omega)) D.toCentres hD hE⟩

/-- **The conditional classifier theorem for the design of the paper's program with ONLY
Agent-side hypotheses (every `n ≥ 16 384`).** The design is `paperDesign n fT wT` (Part 157).
IF `E₁` is a measurable event of the retained data with `Pr(HP n ∩ E₁ᶜ) ≤ δ_extra`, and on
`HP n ∩ {H̄_W ≤ h_W} ∩ E₁` the Agent frame bound `c_frame/n` and the Agent replacement root `h_A`
hold, THEN the program succeeds with probability at least `99/100` for the actual random
networks. Every World hypothesis is PROVED. -/
theorem classifier_paper_agent (hn : 16384 ≤ n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {E₁ : Set (Ret n)}
    (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_conditional_agent hn (constC (by omega)) (constK (by omega)) fT wT hf hw t
    hE₁ hextra hFA hRA

/-- The same at `n = 16 384`. -/
theorem classifier_paper_agent_16384
    (fT wT : Ret 16384 → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {E₁ : Set (Ret 16384)}
    (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres 16384)).real (HP 16384 ∩ E₁ᶜ) ≤ δextraL)
    (hFA : FRAME_A_hyp (paperDesign 16384 fT wT hf hw) (cfL / (16384 : ℕ))
      (goodSet (HP 16384) E₁ (HbarW (paperDesign 16384 fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign 16384 fT wT hf hw) t hAL
      (goodSet (HP 16384) E₁ (HbarW (paperDesign 16384 fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 16384).prod (sampMeas (10 ^ 12) 16384)).real
      {x | successNet x.1 t
        (progOut (paperDesign 16384 fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_agent le_rfl fT wT hf hw t hE₁ hextra hFA hRA

/-- **The same with the two angle events proved** (every `n ≥ 16 384`): the Agent hypotheses are
needed only on `HP n ∩ {H̄_W ≤ h_W} ∩ (E_{θ−} ∩ E_{θ+} ∩ E_A)`, and `E_A` needs
`6.146·10⁻⁶ + Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_extra`. -/
theorem classifier_paper_agent_window (hn : 16384 ≤ n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {EA : Set (Ret n)}
    (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real
      (HP n ∩ Ethm (paperCentres n) ∩ Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hsum : δAng + δA ≤ δextraL)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n) ∩ EA)
        (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n) ∩ EA)
        (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_conditional_agent_window hn (constC (by omega)) (constK (by omega)) fT wT hf
    hw t hEA hA hsum hFA hRA

/-- The World part of the ledger for the centre of the paper, with the two endpoint tails of
Part 156: `δPap + vPap/h_W² + B_+ + B_- ≤ 0.0060527`. -/
lemma world_ledger_pap :
    δPap + vPap / hWL ^ 2 + 146335214251 / 10 ^ 14 + 1694618447832 / 10 ^ 15 ≤
      60527 / 10 ^ 7 := by
  unfold δPap vPap hWL; norm_num

/-- **A free charge `δ_extra` of the other events** (every `n ≥ 16 384`, `paperDesign`): the
failure probability is at most `0.0060527 + δ_extra + 2 e^{−100}` (the ledger of the paper has
`δ_extra = 0.001104285235085`; the level `99/100` needs `δ_extra ≤ 0.0039`). -/
theorem classifier_paper_agent_charges (hn : 16384 ≤ n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {E₁ : Set (Ret n)}
    (hE₁ : MeasurableSet E₁) {δextra : ℝ}
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextra)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
        (failNet (paperDesign n fT wT hf hw) t aL (10 ^ 12)) ≤
      60527 / 10 ^ 7 + δextra + 2 * exp (-100) := by
  have hC := constC (n := n) (by omega)
  have hK := constK (n := n) (by omega)
  have h := classifier_networks_charges_hell hn gaussFrameMGF (paperDesign n fT wT hf hw) t
    (events_paper hn hC hK (paperDesign n fT wT hf hw) rfl (fun _ => rfl) hE₁ hextra)
    (frame_w_paper hn hC (paperCentres n) rfl (fun _ hc => hc.1.1)) hFA hRA
  have h2 := world_ledger_pap
  linarith

/-- **The retained World window for the design of the paper's program** (every `n ≥ 16 384`),
with no hypothesis on the constants (Lemma `t7:p02:window`). -/
theorem theta_window_paper' (hn : 16384 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) {c : Ret n} (hc : c ∈ HP n) :
    0 < D.tau0 c ∧
      D.tau0 c ^ 2 = 2 / (mW n : ℝ) * normSq (D.bW c.1.1) *
        (2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1) ∧
      994 / 1000 ≤ 2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ∧
      2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ≤ 1057 / 1000 ∧
      (c ∈ Ethm D.toCentres → 465 / 1000 ≤ thetaIn D c) ∧
      (c ∈ Ethp D.toCentres → thetaIn D c ≤ 528 / 1000) :=
  theta_window_paper hn (constC (by omega)) (constK (by omega)) D hD hτ hc

/-- The charge of the hidden World event of the paper's design, as a statement about the retained
data: `Pr((HP n)ᶜ) ≤ 0.00163204` (`n ≥ 16 384`; no hypothesis on the constants). -/
theorem HP_charge (hn : 16384 ≤ n) (D : Centres n) : (retDist D).real (HP n)ᶜ ≤ δPap := by
  unfold HP
  rw [hid_charge D (measurableSet_GPap (by omega))]
  exact pap_charge hn

end BstLean.Part159

open BstLean.Part159 in
#print axioms paper_world
open BstLean.Part159 in
#print axioms classifier_paper_agent
open BstLean.Part159 in
#print axioms classifier_paper_agent_16384
open BstLean.Part159 in
#print axioms classifier_paper_agent_window
open BstLean.Part159 in
#print axioms classifier_paper_agent_charges
open BstLean.Part159 in
#print axioms theta_window_paper'
open BstLean.Part159 in
#print axioms HP_charge
