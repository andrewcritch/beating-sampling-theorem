import BstLean.Part160Best4
import BstLean.Part160Best5
import BstLean.Part159All

/-!
# Part 160 (file `Comb`): the classifier theorem for the paper's design with the World stage of
Part 159 and the Agent frame bound of Part 160

Do not use `sorry`, `native_decide` or `axiom`.

* `classifier_paper_comb23` (every `n ≥ 23 000`, Agent frame bound `3.05/n`, centre charge with
  changes (A)–(D)) and `classifier_paper_comb` (every `n ≥ 24 500`, `3.35/n`): for `paperDesign n fT wT`, the program succeeds
  with probability at least `99/100`; the ONLY remaining hypothesis is the Agent replacement
  `REPLA_mix_hyp` on `HP n ∩ {H̄_W ≤ h_W} ∩ E_{θ−} ∩ E_{θ+}`.
  * World (Part 159): hidden event `H = HP n`, `Pr((HP n)ᶜ) ≤ 0.00163204`, Hellinger moment
    `≤ 7.37·10⁻⁹`, frame bound `1.377/n` on `HP n`, the window `0.465 ≤ θ_in ≤ 0.528` and `τ₀ > 0`
    on `HP n ∩ E_{θ−} ∩ E_{θ+}`; the two angle events have charge `≤ δAng = 6.146·10⁻⁶`.
  * Agent (Part 160): the frame bound `3.35/n` on seven Agent events of total charge `≤ 0.00034`.
  * Total charge: `0.00163204 + 7.37·10⁻⁹/h_W² + 6.146·10⁻⁶ + 0.00034 ≤ 0.0063`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156

variable {n : ℕ}

lemma thetaIn_eq (D : Design n) (c : Ret n) :
    BstLean.Part159.thetaIn D c = thetaC c.1.2 (D.tau0 c) := by
  unfold BstLean.Part159.thetaIn thetaC
  rw [rhoC_sqP]

/-- **The window of Part 159 gives `WINDOW_hyp`** on every set inside
`HP n ∩ E_{θ−} ∩ E_{θ+}`, for the design of the paper. -/
theorem window_paper (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {E : Set (Ret n)}
    (hE : E ⊆ BstLean.Part159.HP n ∩ (BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n))) :
    WINDOW_hyp (paperDesign n fT wT hf hw) E := by
  intro c hc
  obtain ⟨hH, hm, hp⟩ := hE hc
  obtain ⟨hτ, -, -, -, h1, h2⟩ := BstLean.Part159.theta_window_paper' hn
    (paperDesign n fT wT hf hw) rfl (fun _ => rfl) hH
  have e := thetaIn_eq (paperDesign n fT wT hf hw) c
  refine ⟨hτ, ?_, ?_⟩
  · have := h1 hm; rw [e] at this; linarith
  · have := h2 hp; rw [e] at this; linarith

/-- **The classifier theorem for the paper's design, every `n ≥ 24 500`, with the Agent
replacement as the only hypothesis.** The World stage is Part 159 (`paper_world`,
`theta_window_paper'`, `extra_angle`); the Agent frame bound is Part 160
(`classifier_agentframe4_24500`). -/
theorem classifier_paper_comb (hn : 24500 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  set D := paperDesign n fT wT hf hw with hDd
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n)
    with hE₁d
  have hE₁ : MeasurableSet E₁ :=
    (BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)
  obtain ⟨hW1, hW2⟩ := BstLean.Part159.paper_world hn16 D rfl (fun _ => rfl)
  -- the charge of the angle events
  have hang : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng := by
    have h := BstLean.Part159.extra_angle hn16 (paperCentres n) (BstLean.Part159.HP n) Set.univ
    have e1 : BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
        Set.univ = E₁ := by rw [Set.inter_univ]
    rw [e1, Set.compl_univ, Set.inter_empty, measureReal_empty, add_zero] at h
    exact h
  have hEv := hW1 hE₁ hang
  have hsubH : goodSet (BstLean.Part159.HP n) E₁ (HbarW D) hWL ⊆ BstLean.Part159.HP n :=
    fun c hc => hc.1.1
  have hWin : WINDOW_hyp D (goodSet (BstLean.Part159.HP n) E₁ (HbarW D) hWL) :=
    window_paper hn16 fT wT hf hw (fun c hc => ⟨hc.1.1, hc.2⟩)
  have hsum : BstLean.Part159.δPap + BstLean.Part159.vPap / hWL ^ 2 + BstLean.Part159.δAng +
      34 / 100000 ≤ 63 / 10 ^ 4 := by
    unfold BstLean.Part159.δPap BstLean.Part159.vPap BstLean.Part159.δAng hWL
    norm_num
  exact classifier_agentframe4_24500 hn D (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv hsum hWin (hW2 hsubH) hRA

/-- **The classifier theorem for the paper's design, every `n ≥ 23 000`, with the Agent
replacement as the only hypothesis.** The World stage is Part 159 (`paper_world`,
`theta_window_paper'`, `extra_angle`); the Agent frame bound is Part 160
(`classifier_agentframe5_23000`). -/
theorem classifier_paper_comb23 (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  set D := paperDesign n fT wT hf hw with hDd
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n)
    with hE₁d
  have hE₁ : MeasurableSet E₁ :=
    (BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)
  obtain ⟨hW1, hW2⟩ := BstLean.Part159.paper_world hn16 D rfl (fun _ => rfl)
  -- the charge of the angle events
  have hang : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng := by
    have h := BstLean.Part159.extra_angle hn16 (paperCentres n) (BstLean.Part159.HP n) Set.univ
    have e1 : BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
        Set.univ = E₁ := by rw [Set.inter_univ]
    rw [e1, Set.compl_univ, Set.inter_empty, measureReal_empty, add_zero] at h
    exact h
  have hEv := hW1 hE₁ hang
  have hsubH : goodSet (BstLean.Part159.HP n) E₁ (HbarW D) hWL ⊆ BstLean.Part159.HP n :=
    fun c hc => hc.1.1
  have hWin : WINDOW_hyp D (goodSet (BstLean.Part159.HP n) E₁ (HbarW D) hWL) :=
    window_paper hn16 fT wT hf hw (fun c hc => ⟨hc.1.1, hc.2⟩)
  have hsum : BstLean.Part159.δPap + BstLean.Part159.vPap / hWL ^ 2 + BstLean.Part159.δAng +
      34 / 100000 ≤ 63 / 10 ^ 4 := by
    unfold BstLean.Part159.δPap BstLean.Part159.vPap BstLean.Part159.δAng hWL
    norm_num
  exact classifier_agentframe5_23000 hn D (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv hsum hWin (hW2 hsubH) hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms window_paper
open BstLean.Part160 in
#print axioms classifier_paper_comb
open BstLean.Part160 in
#print axioms classifier_paper_comb23
