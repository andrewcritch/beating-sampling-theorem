import BstLean.Part182FrameTI
import BstLean.Part182Ledger
import BstLean.Part182EvW
import BstLean.Part181Comb

/-!
# Part 182 (file `Comb`): the frame junction at `n ≥ 22 000` with the covariance event (CONDITIONAL on TI)

No proof is left open; no `native_decide` or `axiom` is used.

* `roomT = 0.0025`: the room that the frame constant `1.82` (in place of `2.765`) releases for the
  free Agent event, after the charge `10⁻⁴` of the covariance event `SCovT`.
* `FREE22T_stmt`: Part 181's `FREE22_stmt` with the extra hypotheses `GeoT n` and
  `TI_hyp n 0.386 0.638 0.582 10⁻¹⁸`, and the room `roomA + roomX + roomT`.
* **`classifier_paper_free22T : FREE22T_stmt`**. Proof: as Part 181's `classifier_paper_free22`,
  with the free Agent event intersected with `agentEv D (SXM22 n) ∩ agentEv D (SCovT n)` (charges
  `5·10⁻⁵` and `10⁻⁴`; the second from `TI_hyp` by `SCovT_ret_charge`), the frame `1.82/n`
  (`frameA_T_22000`) and the ledger `classifier_frame_182` (budget `0.009569`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181
open BstLean.Part163 (Eframe roomA events_with_Eframe)

variable {n : ℕ}

/-- **The extra room `0.0025`** that the frame constant `1.82` gives to the free Agent event. -/
noncomputable def roomT : ℝ := 25 / 10000

lemma roomT_eq : roomT = 25 / 10000 := rfl

/-- **The frame junction at `n ≥ 22 000` with the covariance event**, CONDITIONAL on the
geometry `GeoT n` and the two-input hypothesis `TI_hyp`. -/
def FREE22T_stmt : Prop :=
  ∀ {n : ℕ} (_hn : 22000 ≤ n) (_hgeo : GeoT n)
    (_hTI : TI_hyp n (386 / 1000) (638 / 1000) (582 / 1000) (1 / 10 ^ 18))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (_hEA : MeasurableSet EA) {δA : ℝ}
    (_hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (_hroom : δA ≤ BstLean.Part163.roomA + roomX + roomT)
    (_hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩
          BstLean.Part163.Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL)),
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)}

/-- **The frame junction at `n ≥ 22 000` with the covariance event** (proof). -/
theorem classifier_paper_free22T : FREE22T_stmt := by
  intro n hn hgeo hTI fT wT hf hw t EA hEA δA hA hroom hRA
  have hn16 : 16384 ≤ n := by omega
  set D := paperDesign n fT wT hf hw with hDd
  set S := agentEv D (SXM22 n) ∩ agentEv D (SCovT n) with hSd
  have hSm : MeasurableSet S := (measurableSet_agentEv D (measurableSet_SXM22 n)).inter
    (measurableSet_agentEv D (measurableSet_SCovT n))
  set EA' := EA ∩ S with hEA'
  have hEA'm : MeasurableSet EA' := hEA.inter hSm
  -- the charge of the enlarged Agent event
  have hA' : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ) ≤
      δA + 5 / 100000 + 1 / 10 ^ 4 := by
    have hsub : BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ ⊆
        ((BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
          BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪ (agentEv D (SXM22 n))ᶜ) ∪
          (agentEv D (SCovT n))ᶜ := by
      intro c hc
      by_cases h : c ∈ EA
      · by_cases h1 : c ∈ agentEv D (SXM22 n)
        · right; intro h2; exact hc.2 ⟨h, h1, h2⟩
        · left; right; exact h1
      · left; left; exact ⟨hc.1, h⟩
    have hS1 := SXM22_ret_charge hn fT wT hf hw
    have hS2 := SCovT_ret_charge hn hgeo hTI fT wT hf hw
    calc _ ≤ (retDist (paperCentres n)).real (((BstLean.Part159.HP n ∩
            BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪
            (agentEv D (SXM22 n))ᶜ) ∪ (agentEv D (SCovT n))ᶜ) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (retDist (paperCentres n)).real ((BstLean.Part159.HP n ∩
            BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪
            (agentEv D (SXM22 n))ᶜ) + (retDist (paperCentres n)).real (agentEv D (SCovT n))ᶜ :=
          measureReal_union_le _ _
      _ ≤ (δA + 5 / 100000) + 1 / 10 ^ 4 :=
          add_le_add ((measureReal_union_le _ _).trans (add_le_add hA hS1)) hS2
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'
    with hE₁d
  have hE₁ : MeasurableSet E₁ :=
    ((BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)).inter
      hEA'm
  obtain ⟨hW1, hW2⟩ := BstLean.Part159.paper_world hn16 D rfl (fun _ => rfl)
  have hch : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng + (δA + 5 / 100000 + 1 / 10 ^ 4) := by
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
  have hFA : FRAME_A_hyp D (182 / 100 / n) G :=
    frameA_T_22000 hn D (paperDesign_agentCentre fT wT hf hw) hWin
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
      (BstLean.Part159.δAng + (δA + 5 / 100000 + 1 / 10 ^ 4) + 33515 / 10 ^ 8) ≤ 9569 / 10 ^ 6 := by
    unfold roomA at hroom
    rw [roomX_eq, roomT_eq] at hroom
    linarith
  exact classifier_frame_182 hn D t hEv' hsum hFW hFA hRA'

end BstLean.Part182

open BstLean.Part182 in
#print axioms classifier_paper_free22T
