import BstLean.Part184Def
import BstLean.Part184FFrame
import BstLean.Part184FLed
import BstLean.Part184FCov
import BstLean.Part181Comb

/-!
# Part 184 (file `FComb`): the frame junction at `n ≥ 18 500` (TI-lite `λ = 0.735`), CONDITIONAL on
the two-input hypothesis (copy of `FComb`)

No proof is left open; no `native_decide` or `axiom` is used.

**`FREE185_of_TI`**: `(∀ n ≥ 18 500, TI_hyp n 0.374 0.650 0.735 10⁻¹⁸) → BstLean.Part184.FREE185_stmt`, with the moment
event `SXM185` (charge `5·10⁻⁵`, file `FW`), the covariance event `SCovT185` (charge `10⁻⁵`,
geometry `geoT185_holds`, file `FCov`), the frame `2.19/n` (`frameA_T_18500`, file `FFrame`) and
the ledger `classifier_frame_185` (budget `0.006499`, tails `≤ 0.0035`, file `FLed`):
`0.0063 − 34·10⁻⁵ + roomX + roomT185 + 5·10⁻⁵ + 10⁻⁵ + 33 515·10⁻⁸ = 0.00625515 ≤ 0.006499 (roomT185 = −0.0007)`.
-/

namespace BstLean.Part183.F185

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181
open BstLean.Part163 (Eframe roomA events_with_Eframe)

variable {n : ℕ}

/-- **The frame junction at `n ≥ 21 000`, CONDITIONAL on the two-input hypothesis**: if
`TI_hyp n 0.383 0.641 0.72 10⁻¹⁸` holds for every `n ≥ 21 000`, then `BstLean.Part184.FREE185_stmt` holds. -/
theorem FREE185_of_TI
    (hTI : ∀ n : ℕ, 18500 ≤ n → BstLean.Part182.TI_hyp n (374 / 1000) (650 / 1000) (735 / 1000) (1 / 10 ^ 18)) :
    BstLean.Part184.FREE185_stmt := by
  intro n hn fT wT hf hw t EA hEA δA hA hroom hRA
  have hgeo := geoT185_holds hn
  have hTIn := hTI n hn
  have hn16 : 16384 ≤ n := by omega
  set D := paperDesign n fT wT hf hw with hDd
  set S := agentEv D (SXM185 n) ∩ agentEv D (SCovT185 n) with hSd
  have hSm : MeasurableSet S := (measurableSet_agentEv D (measurableSet_SXM185 n)).inter
    (measurableSet_agentEv D (measurableSet_SCovT185 n))
  set EA' := EA ∩ S with hEA'
  have hEA'm : MeasurableSet EA' := hEA.inter hSm
  -- the charge of the enlarged Agent event
  have hA' : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ) ≤
      δA + 5 / 100000 + 1 / 10 ^ 5 := by
    have hsub : BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ ⊆
        ((BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
          BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪ (agentEv D (SXM185 n))ᶜ) ∪
          (agentEv D (SCovT185 n))ᶜ := by
      intro c hc
      by_cases h : c ∈ EA
      · by_cases h1 : c ∈ agentEv D (SXM185 n)
        · right; intro h2; exact hc.2 ⟨h, h1, h2⟩
        · left; right; exact h1
      · left; left; exact ⟨hc.1, h⟩
    have hS1 := SXM185_ret_charge hn fT wT hf hw
    have hS2 := SCovT185_ret_charge hn hgeo hTIn fT wT hf hw
    calc _ ≤ (retDist (paperCentres n)).real (((BstLean.Part159.HP n ∩
            BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪
            (agentEv D (SXM185 n))ᶜ) ∪ (agentEv D (SCovT185 n))ᶜ) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (retDist (paperCentres n)).real ((BstLean.Part159.HP n ∩
            BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪
            (agentEv D (SXM185 n))ᶜ) + (retDist (paperCentres n)).real (agentEv D (SCovT185 n))ᶜ :=
          measureReal_union_le _ _
      _ ≤ (δA + 5 / 100000) + 1 / 10 ^ 5 :=
          add_le_add ((measureReal_union_le _ _).trans (add_le_add hA hS1)) hS2
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'
    with hE₁d
  have hE₁ : MeasurableSet E₁ :=
    ((BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)).inter
      hEA'm
  obtain ⟨hW1, hW2⟩ := BstLean.Part159.paper_world hn16 D rfl (fun _ => rfl)
  have hch : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng + (δA + 5 / 100000 + 1 / 10 ^ 5) := by
    have h := BstLean.Part159.extra_angle hn16 (paperCentres n) (BstLean.Part159.HP n) EA'
    exact h.trans (add_le_add le_rfl hA')
  have hEv := hW1 hE₁ hch
  have hEv' := events_with_Eframe hn16 D (paperDesign_tauWorld fT wT hf hw) hEv
  set G := goodSet (BstLean.Part159.HP n) (E₁ ∩ Eframe D) (HbarW D) hWL with hGd
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
  have hFr : ∀ c ∈ G, c ∈ Eframe D := fun c hc => hc.2.2
  have hFA : FRAME_A_hyp D (219 / 100 / n) G :=
    frameA_T_18500 hn D (paperDesign_agentCentre fT wT hf hw) hWin
      (fun c hc => (hFr c hc).1.1.1.1.1.1)
      (fun c hc => hc.2.1.2.2.1)
      (fun c hc => (hFr c hc).1.1.2)
      (fun c hc => (hFr c hc).1.2)
      (fun c hc => (hFr c hc).2)
      (fun c hc => hc.2.1.2.2.2)
  have hRA' : REPLA_mix_hyp D t hAL G := by
    intro c hc
    refine hRA c ⟨hc.1, ⟨⟨hc.2.1.1, hc.2.1.2.1⟩, hc.2.2⟩⟩
  have hsum : BstLean.Part159.δPap + BstLean.Part159.vPap / hWL ^ 2 +
      (BstLean.Part159.δAng + (δA + 5 / 100000 + 1 / 10 ^ 5) + 33515 / 10 ^ 8) ≤ 6499 / 1000000 := by
    unfold roomA at hroom
    rw [roomX_eq, BstLean.Part184.roomT185_eq] at hroom
    linarith
  exact classifier_frame_185 hn D t hEv' hsum hFW hFA hRA'

end BstLean.Part183.F185

open BstLean.Part183.F185 in
#print axioms FREE185_of_TI
