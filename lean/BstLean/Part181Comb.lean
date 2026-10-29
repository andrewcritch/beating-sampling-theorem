import BstLean.Part181Def
import BstLean.Part181Frame
import BstLean.Part181Ledger

/-!
# Part 181 (file `Comb`): the frame junction at `n ≥ 22 000` (`FREE22_stmt` proved)

No proof is left open; no `native_decide` or `axiom` is used.

**`classifier_paper_free22 : FREE22_stmt`**: Part 163's `classifier_paper_free23` with the floor
`22 000` and the room `roomA + roomX` (`roomX = 6·10⁻⁴`). The proof:

* the free Agent event `E_A` is intersected with the event `agentEv D (SXM22 n)` (charge
  `5·10⁻⁵`, file `W`); Part 163's frame event `Eframe` is kept (charge `33 515·10⁻⁸`), because
  the Agent replacement is given on a set that contains it;
* the Agent frame bound is `2.765/n` (file `Frame`), from `Eframe`, `SXM22` and the World window
  `0.465 ≤ θ_in ≤ 0.528` (Part 159);
* the ledger is `classifier_frame_2765` (file `Ledger`) with the charge budget `0.0069452`:
  `0.0063 − 34·10⁻⁵ + roomX + 5·10⁻⁵ + 33 515·10⁻⁸ ≤ 0.0069452`.

The Agent replacement hypothesis is used on a SUBSET of the set where it is given (the good set
with the extra event `SXM22`); `REPLA_mix_hyp` is a statement for every point of a set, so this is
sound.
-/

namespace BstLean.Part181

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part163 (Eframe roomA events_with_Eframe)

variable {n : ℕ}

/-- **The frame junction at `n ≥ 22 000`.** -/
theorem classifier_paper_free22 : FREE22_stmt := by
  intro n hn fT wT hf hw t EA hEA δA hA hroom hRA
  have hn16 : 16384 ≤ n := by omega
  set D := paperDesign n fT wT hf hw with hDd
  set S := agentEv D (SXM22 n) with hSd
  have hSm : MeasurableSet S := measurableSet_agentEv D (measurableSet_SXM22 n)
  set EA' := EA ∩ S with hEA'
  have hEA'm : MeasurableSet EA' := hEA.inter hSm
  -- the charge of the enlarged Agent event
  have hA' : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ) ≤
      δA + 5 / 100000 := by
    have hsub : BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ ⊆
        (BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
          BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪ Sᶜ := by
      intro c hc
      by_cases h : c ∈ EA
      · right; intro hS; exact hc.2 ⟨h, hS⟩
      · left; exact ⟨hc.1, h⟩
    have hS := SXM22_ret_charge hn fT wT hf hw
    calc _ ≤ (retDist (paperCentres n)).real ((BstLean.Part159.HP n ∩
            BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪
            Sᶜ) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ δA + 5 / 100000 := add_le_add hA hS
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'
    with hE₁d
  have hE₁ : MeasurableSet E₁ :=
    ((BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)).inter
      hEA'm
  obtain ⟨hW1, hW2⟩ := BstLean.Part159.paper_world hn16 D rfl (fun _ => rfl)
  have hch : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng + (δA + 5 / 100000) := by
    have h := BstLean.Part159.extra_angle hn16 (paperCentres n) (BstLean.Part159.HP n) EA'
    exact h.trans (add_le_add le_rfl hA')
  have hEv := hW1 hE₁ hch
  have hEv' := events_with_Eframe hn16 D (paperDesign_tauWorld fT wT hf hw) hEv
  set G := goodSet (BstLean.Part159.HP n) (E₁ ∩ Eframe D) (HbarW D) hWL with hGd
  -- the window `0.465 ≤ θ_in ≤ 0.528` on the good set
  have hWin : ∀ c ∈ G, 0 < D.tau0 c ∧ 46 / 100 ≤ thetaC c.1.2 (D.tau0 c) ∧
      thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000 := by
    intro c hc
    obtain ⟨hτ, -, -, -, h1, h2⟩ := BstLean.Part159.theta_window_paper' hn16 D rfl (fun _ => rfl)
      hc.1.1
    have e := BstLean.Part160.thetaIn_eq D c
    have hm : c ∈ BstLean.Part159.Ethm (paperCentres n) := hc.2.1.1.1
    have hp : c ∈ BstLean.Part159.Ethp (paperCentres n) := hc.2.1.1.2
    refine ⟨hτ, ?_, ?_⟩
    · have := h1 hm; rw [e] at this; linarith
    · have := h2 hp; rw [e] at this; exact this
  have hFW := hW2 (E := G) (fun c hc => hc.1.1)
  -- the frame bound `2.78/n`
  have hFr : ∀ c ∈ G, c ∈ Eframe D := fun c hc => hc.2.2
  have hFA : FRAME_A_hyp D (2765 / 1000 / n) G :=
    frameA_22000 hn D (paperDesign_agentCentre fT wT hf hw) hWin
      (fun c hc => (hFr c hc).1.1.1.1.1.1)
      (fun c hc => hc.2.1.2.2)
      (fun c hc => (hFr c hc).1.1.2)
      (fun c hc => (hFr c hc).1.2)
      (fun c hc => (hFr c hc).2)
  -- the Agent replacement on the smaller good set
  have hRA' : REPLA_mix_hyp D t hAL G := by
    intro c hc
    refine hRA c ⟨hc.1, ⟨⟨hc.2.1.1, hc.2.1.2.1⟩, hc.2.2⟩⟩
  have hsum : BstLean.Part159.δPap + BstLean.Part159.vPap / hWL ^ 2 +
      (BstLean.Part159.δAng + (δA + 5 / 100000) + 33515 / 10 ^ 8) ≤ 69452 / 10 ^ 7 := by
    unfold roomA at hroom
    rw [roomX_eq] at hroom
    linarith
  exact classifier_frame_2765 hn D t hEv' hsum hFW hFA hRA'

end BstLean.Part181

open BstLean.Part181 in
#print axioms classifier_paper_free22
