import BstLean.Part184Def
import BstLean.Part186FFrame
import BstLean.Part186FLed
import BstLean.Part186FCov
import BstLean.Part181Comb

/-!
# Part 186 (file `FComb`): the frame junction at `n ≥ 16 500`, CONDITIONAL on the two-input
hypothesis with `λ = 0.647` (the ε-net E block, files `Part185D*`) (copy of `FComb`)

No proof is left open; no `native_decide` or `axiom` is used.

**`FREE165_of_TI`**: `(∀ n ≥ 16 500, TI_hyp n 0.370 0.655 0.647 10⁻¹⁸) → BstLean.Part186.FREE165_stmt`,
with the moment event `SXM165` (`M = 1.119`, charge `5·10⁻⁵`, file `GW`), the covariance event
`SCovT165` (charge `10⁻⁵`, geometry `geoT165_holds`: pairs have `0.370 ≤ x·x' ≤ 0.655`, file `GCov`),
the frame `2.082/n` (`frameA_T_16500`, file `GFrame`) and the ledger `classifier_frame_165` (budget
`0.004265`, tails `≤ 0.005734`, file `GLed`):
`0.0063 − 34·10⁻⁵ + roomX + roomT165 + 5·10⁻⁵ + 10⁻⁵ + 33 515·10⁻⁸ = 0.00426415 ≤ 0.004265`
(`roomT165 = −0.002691`).
-/

namespace BstLean.Part186

/-- **The extra room `−0.002691` at `n ≥ 16 500`.** -/
noncomputable def roomT165 : ℝ := -(2691 / 1000000)

lemma roomT165_eq : roomT165 = -(2691 / 1000000) := rfl

/-- **The frame junction at `n ≥ 16 500`.** -/
def FREE165_stmt : Prop := BstLean.Part183.FREEg_stmt 16500 roomT165

end BstLean.Part186

namespace BstLean.Part183.F165

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181
open BstLean.Part163 (Eframe roomA events_with_Eframe)

variable {n : ℕ}

/-- **The frame junction at `n ≥ 21 000`, CONDITIONAL on the two-input hypothesis**: if
`TI_hyp n 0.383 0.641 0.72 10⁻¹⁸` holds for every `n ≥ 21 000`, then `BstLean.Part186.FREE165_stmt` holds. -/
theorem FREE165_of_TI
    (hTI : ∀ n : ℕ, 16500 ≤ n → BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (647 / 1000) (1 / 10 ^ 18)) :
    BstLean.Part186.FREE165_stmt := by
  intro n hn fT wT hf hw t EA hEA δA hA hroom hRA
  have hgeo := geoT165_holds hn
  have hTIn := hTI n hn
  have hn16 : 16384 ≤ n := by omega
  set D := paperDesign n fT wT hf hw with hDd
  set S := agentEv D (SXM165 n) ∩ agentEv D (SCovT165 n) with hSd
  have hSm : MeasurableSet S := (measurableSet_agentEv D (measurableSet_SXM165 n)).inter
    (measurableSet_agentEv D (measurableSet_SCovT165 n))
  set EA' := EA ∩ S with hEA'
  have hEA'm : MeasurableSet EA' := hEA.inter hSm
  -- the charge of the enlarged Agent event
  have hA' : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ) ≤
      δA + 5 / 100000 + 1 / 10 ^ 5 := by
    have hsub : BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ ⊆
        ((BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
          BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪ (agentEv D (SXM165 n))ᶜ) ∪
          (agentEv D (SCovT165 n))ᶜ := by
      intro c hc
      by_cases h : c ∈ EA
      · by_cases h1 : c ∈ agentEv D (SXM165 n)
        · right; intro h2; exact hc.2 ⟨h, h1, h2⟩
        · left; right; exact h1
      · left; left; exact ⟨hc.1, h⟩
    have hS1 := SXM165_ret_charge hn fT wT hf hw
    have hS2 := SCovT165_ret_charge hn hgeo hTIn fT wT hf hw
    calc _ ≤ (retDist (paperCentres n)).real (((BstLean.Part159.HP n ∩
            BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪
            (agentEv D (SXM165 n))ᶜ) ∪ (agentEv D (SCovT165 n))ᶜ) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (retDist (paperCentres n)).real ((BstLean.Part159.HP n ∩
            BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪
            (agentEv D (SXM165 n))ᶜ) + (retDist (paperCentres n)).real (agentEv D (SCovT165 n))ᶜ :=
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
  have hFA : FRAME_A_hyp D (2082 / 1000 / n) G :=
    frameA_T_16500 hn D (paperDesign_agentCentre fT wT hf hw) hWin
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
      (BstLean.Part159.δAng + (δA + 5 / 100000 + 1 / 10 ^ 5) + 33515 / 10 ^ 8) ≤ 853 / 200000 := by
    unfold roomA at hroom
    rw [roomX_eq, BstLean.Part186.roomT165_eq] at hroom
    linarith
  exact classifier_frame_165 hn D t hEv' hsum hFW hFA hRA'

/-- `FREE165_of_TI` with the junction statement unfolded: `FREEg_stmt 16500 (−0.002691)`. -/
theorem FREE165g_of_TI
    (hTI : ∀ n : ℕ, 16500 ≤ n → BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (647 / 1000) (1 / 10 ^ 18)) :
    BstLean.Part183.FREEg_stmt 16500 (-(2691 / 1000000)) :=
  FREE165_of_TI hTI

end BstLean.Part183.F165

open BstLean.Part183.F165 in
#print axioms FREE165_of_TI
open BstLean.Part183.F165 in
#print axioms FREE165g_of_TI

namespace BstLean.Part186

/-- **The frame junction at `n ≥ 16 500`** (headline in `BstLean.Part186`): from the two-input
hypothesis on `[0.370, 0.655]` at `λ = 0.647`, `FREEg_stmt 16500 (−0.002691)`. -/
theorem FREE165g_of_TI
    (hTI : ∀ n : ℕ, 16500 ≤ n → BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (647 / 1000) (1 / 10 ^ 18)) :
    BstLean.Part183.FREEg_stmt 16500 (-(2691 / 1000000)) :=
  BstLean.Part183.F165.FREE165g_of_TI hTI

end BstLean.Part186

#print axioms BstLean.Part186.FREE165g_of_TI
