import BstLean.Part159Hat

/-!
# Part 159 (file `Final`): the classifier theorem with ONLY Agent-side hypotheses

Role: `delegations/statements/p159-spec.md`, item 2. Do not use `sorry`, `native_decide` or
`axiom`.

The design: ANY `Design n` whose World centre is the computed centre `bhat = ψ_s(W₂ h̄₁)` of
Parts 137 and 140 and whose scalar is `τ₀ = tauHat (W₁, W₂)` of Part 140. The Agent centre and the
mixture table are free. `hatDesign` builds such a design from an Agent centre and a table.

* `classifier_networks_conditional_agent`: for every `n ≥ 16 384`: IF an event `E₁` of the retained
  data has `Pr(HW n ∩ E₁ᶜ) ≤ δ_extra = 0.001104285235085`, and on `HW n ∩ {H̄_W ≤ h_W} ∩ E₁` the
  Agent frame bound `1.743/n` and the Agent replacement root `h_A` hold, THEN the program succeeds
  with probability at least `99/100`. The World hypotheses of Part 158 (`FRAME_W_hyp`, the hidden
  event with its charge, the Hellinger moment) are PROVED.
* `classifier_networks_agent_charges`: the same with a free charge `δ_extra`: the failure
  probability is at most `0.0060423 + δ_extra`.
* `classifier_networks_agent_success`: success `≥ 99/100` if `δ_extra ≤ 0.0039`.

It is still a CONDITIONAL theorem: `FRAME_A_hyp`, `REPLA_mix_hyp` and the charge of `E₁` are
hypotheses. The centre is NOT the binomial centre of the paper.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part137 (bhat measurable_bhat)
open BstLean.Part140
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- **A design with the computed World centre**: `b_W = bhat (W₁, W₂)`, `τ₀ = tauHat (W₁, W₂)`;
the Agent centre `bA` and the mixture table `mix` are arguments. -/
noncomputable def hatDesign (hn : 1 ≤ n) (bA : WRet n → AHid n → Fin (mA n) → ℝ)
    (mbA : Measurable (fun p : WRet n × AHid n => bA p.1 p.2)) (mix : Ret n → ℝ → ℝ × ℝ)
    (mmix : Measurable (fun p : Ret n × ℝ => mix p.1 p.2)) : Design n where
  bW := bhat
  bA := bA
  mbW := measurable_bhat (by omega)
  mbA := mbA
  tau0 := fun c => tauHat (2 * n) (mW n) c.1.1
  mix := mix
  mtau0 := (measurable_tauHat (by omega)).comp measurable_hidOf
  mmix := mmix

lemma hatDesign_bW (hn : 1 ≤ n) (bA : WRet n → AHid n → Fin (mA n) → ℝ)
    (mbA : Measurable (fun p : WRet n × AHid n => bA p.1 p.2)) (mix : Ret n → ℝ → ℝ × ℝ)
    (mmix : Measurable (fun p : Ret n × ℝ => mix p.1 p.2)) :
    (hatDesign hn bA mbA mix mmix).bW = bhat := rfl

lemma hatDesign_tau0 (hn : 1 ≤ n) (bA : WRet n → AHid n → Fin (mA n) → ℝ)
    (mbA : Measurable (fun p : WRet n × AHid n => bA p.1 p.2)) (mix : Ret n → ℝ → ℝ × ℝ)
    (mmix : Measurable (fun p : Ret n × ℝ => mix p.1 p.2)) (c : Ret n) :
    (hatDesign hn bA mbA mix mmix).tau0 c = tauHat (2 * n) (mW n) c.1.1 := rfl

/-- **The conditional classifier theorem with ONLY Agent-side hypotheses (every `n ≥ 16 384`).**
`D` is a design with the computed World centre `bhat` and the scalar `tauHat`. `HW n` is the
hidden World event (`goodHat n` of Part 140). IF `E₁` is a measurable event of the retained data
with `Pr(HW n ∩ E₁ᶜ) ≤ δ_extra` (the constant of the ledger), and on
`HW n ∩ {H̄_W ≤ h_W} ∩ E₁` the Agent frame bound `c_frame/n` and the Agent replacement root `h_A`
hold, THEN the program `progOut D t a (10¹²)` succeeds with probability at least `99/100` for the
actual random networks. The World frame bound, the hidden charge and the Hellinger moment are
PROVED in Lean (Parts 140, 143, 159). -/
theorem classifier_networks_conditional_agent (hn : 16384 ≤ n) (D : Design n) (hD : D.bW = bhat)
    (hτ : ∀ c : Ret n, D.tau0 c = tauHat (2 * n) (mW n) c.1.1) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist D.toCentres).real (HW n ∩ E₁ᶜ) ≤ δextraL)
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet (HW n) E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet (HW n) E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_frames hn D t
    (events_mono (events_hat hn D hD hτ hE₁ hextra) δHat_le vHat_le le_rfl)
    (frame_w_hat hn D.toCentres hD (fun _ hc => hc.1.1)) hFA hRA

/-- The same at `n = 16 384`. -/
theorem classifier_networks_conditional_agent_16384 (D : Design 16384) (hD : D.bW = bhat)
    (hτ : ∀ c : Ret 16384, D.tau0 c = tauHat (2 * 16384) (mW 16384) c.1.1) (t : ℝ)
    {E₁ : Set (Ret 16384)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist D.toCentres).real (HW 16384 ∩ E₁ᶜ) ≤ δextraL)
    (hFA : FRAME_A_hyp D (cfL / (16384 : ℕ)) (goodSet (HW 16384) E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet (HW 16384) E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 16384).prod (sampMeas (10 ^ 12) 16384)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_agent le_rfl D hD hτ t hE₁ hextra hFA hRA

/-- The World part of the ledger for the computed centre, with the two endpoint tails of Part 156:
`δHat + vHat/h_W² + B_+ + B_- ≤ 0.0060423`. -/
lemma world_ledger_hat :
    δHat + vHat / hWL ^ 2 + 146335214251 / 10 ^ 14 + 1694618447832 / 10 ^ 15 ≤
      60423 / 10 ^ 7 := by
  unfold δHat vHat hWL; norm_num

/-- **The same with a free charge `δ_extra` of the other events**: the failure probability is at
most `0.0060423 + δ_extra + 2 e^{−100}`. -/
theorem classifier_networks_agent_charges (hn : 16384 ≤ n) (D : Design n) (hD : D.bW = bhat)
    (hτ : ∀ c : Ret n, D.tau0 c = tauHat (2 * n) (mW n) c.1.1) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁) {δextra : ℝ}
    (hextra : (retDist D.toCentres).real (HW n ∩ E₁ᶜ) ≤ δextra)
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet (HW n) E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet (HW n) E₁ (HbarW D) hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real (failNet D t aL (10 ^ 12)) ≤
      60423 / 10 ^ 7 + δextra + 2 * exp (-100) := by
  have h := classifier_networks_charges_hell hn gaussFrameMGF D t
    (events_hat hn D hD hτ hE₁ hextra)
    (frame_w_hat hn D.toCentres hD (fun _ hc => hc.1.1)) hFA hRA
  have h2 := world_ledger_hat
  linarith

/-- **Success with a free charge**: if the other events have `Pr(HW n ∩ E₁ᶜ) ≤ 0.0039`, the
program succeeds with probability at least `99/100` (the ledger of the paper has
`δ_extra = 0.001104285235085`). -/
theorem classifier_networks_agent_success (hn : 16384 ≤ n) (D : Design n) (hD : D.bW = bhat)
    (hτ : ∀ c : Ret n, D.tau0 c = tauHat (2 * n) (mW n) c.1.1) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist D.toCentres).real (HW n ∩ E₁ᶜ) ≤ 39 / 10 ^ 4)
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet (HW n) E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet (HW n) E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have h := classifier_networks_agent_charges hn D hD hτ t hE₁ hextra hFA hRA
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h h2 ⊢
  linarith

end BstLean.Part159

open BstLean.Part159 in
#print axioms classifier_networks_conditional_agent
open BstLean.Part159 in
#print axioms classifier_networks_conditional_agent_16384
open BstLean.Part159 in
#print axioms classifier_networks_agent_charges
open BstLean.Part159 in
#print axioms classifier_networks_agent_success
