import BstLean.Part184Def
import BstLean.Part187FrK
import BstLean.Part187LedK
import BstLean.Part186GCov
import BstLean.Part186CovC
import BstLean.Part186GeoP
import BstLean.Part186TC
import BstLean.Part186T7
import BstLean.Part181Comb

/-!
# Part 187 (file `CmbK`): the frame junction at `n ≥ 16 384` with the two-level core covariance,
UNCONDITIONAL (Lemma TI discharged by `TI_two_16384` and `TI_core_16384_k`)

No proof is left open; no `native_decide` or `axiom` is used.

**`FREE16384K_proved : FREEg_stmt 16384 (−0.001845)`**: moment event `SXM16384` (`5·10⁻⁵`), wide
covariance event `SCovT16384` (`λ₀ = 0.647`, `10⁻⁵`), seven core events `SCovP` (`10⁻⁶` each,
windows `geoP_k`, `λ₁ = 0.622 … 0.591`), frame `1.967/n` (sharp `e_b`, file `Kap`) (`frameA_K_16384`), ledger
`classifier_frame_16384K` (tails `≤ 0.004881`, budget `0.005118`):
`0.0063 − 34·10⁻⁵ + roomX + roomT16384K + 5·10⁻⁵ + 10⁻⁵ + 7·10⁻⁶ + 33 515·10⁻⁸ = 0.00511715 ≤ 0.005118`.
-/

namespace BstLean.Part187

/-- **The extra room `−0.001845` at `n ≥ 16 384` (core frame).** -/
noncomputable def roomT16384K : ℝ := -(1845 / 1000000)

lemma roomT16384K_eq : roomT16384K = -(1845 / 1000000) := rfl

end BstLean.Part187

namespace BstLean.Part183.F16384

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181
open BstLean.Part163 (Eframe roomA events_with_Eframe)

variable {n : ℕ}

lemma compl_inter_charge {μ : Measure (Ret n)} [IsFiniteMeasure μ] {A B : Set (Ret n)} {a b : ℝ}
    (hA : μ.real Aᶜ ≤ a) (hB : μ.real Bᶜ ≤ b) : μ.real (A ∩ B)ᶜ ≤ a + b := by
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans (add_le_add hA hB)

/-- **The frame junction at `n ≥ 16 384` with the two-level core covariance** (unconditional). -/
theorem FREE16384K_proved : BstLean.Part183.FREEg_stmt 16384 BstLean.Part187.roomT16384K := by
  intro n hn fT wT hf hw t EA hEA δA hA hroom hRA
  have hgeo := geoT16384_holds hn
  have hTIn := BstLean.Part186.TI_two_16384 n hn
  have hn16 : 16384 ≤ n := hn
  set D := paperDesign n fT wT hf hw with hDd
  set S := agentEv D (SXM16384 n) ∩ agentEv D (SCovT16384 n) ∩ agentEv D (BstLean.Part186.SCovP n (46 / 100) (47 / 100) (311 / 500)) ∩ agentEv D (BstLean.Part186.SCovP n (47 / 100) (48 / 100) (617 / 1000)) ∩ agentEv D (BstLean.Part186.SCovP n (48 / 100) (49 / 100) (153 / 250)) ∩ agentEv D (BstLean.Part186.SCovP n (49 / 100) (50 / 100) (607 / 1000)) ∩ agentEv D (BstLean.Part186.SCovP n (50 / 100) (51 / 100) (301 / 500)) ∩ agentEv D (BstLean.Part186.SCovP n (51 / 100) (52 / 100) (597 / 1000)) ∩ agentEv D (BstLean.Part186.SCovP n (52 / 100) (528 / 1000) (591 / 1000)) with hSd
  have mP : ∀ a b l : ℝ, MeasurableSet (agentEv D (BstLean.Part186.SCovP n a b l)) :=
    fun a b l => measurableSet_agentEv D (BstLean.Part186.measurableSet_SCovP n a b l)
  have hSm : MeasurableSet S :=
    ((((((((measurableSet_agentEv D (measurableSet_SXM16384 n)).inter
      (measurableSet_agentEv D (measurableSet_SCovT16384 n))).inter (mP _ _ _)).inter (mP _ _ _)).inter
      (mP _ _ _)).inter (mP _ _ _)).inter (mP _ _ _)).inter (mP _ _ _)).inter (mP _ _ _)
  have hSc : (retDist (paperCentres n)).real Sᶜ ≤ 5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6 := by
    have h0 := compl_inter_charge (SXM16384_ret_charge hn fT wT hf hw)
      (SCovT16384_ret_charge hn hgeo hTIn fT wT hf hw)
    have h1 := compl_inter_charge h0 (BstLean.Part186.SCovP_ret_charge hn (BstLean.Part186.geoP_0 hn)
      (BstLean.Part186.TI_core_16384_0 n hn) fT wT hf hw)
    have h2 := compl_inter_charge h1 (BstLean.Part186.SCovP_ret_charge hn (BstLean.Part186.geoP_1 hn)
      (BstLean.Part186.TI_core_16384_1 n hn) fT wT hf hw)
    have h3 := compl_inter_charge h2 (BstLean.Part186.SCovP_ret_charge hn (BstLean.Part186.geoP_2 hn)
      (BstLean.Part186.TI_core_16384_2 n hn) fT wT hf hw)
    have h4 := compl_inter_charge h3 (BstLean.Part186.SCovP_ret_charge hn (BstLean.Part186.geoP_3 hn)
      (BstLean.Part186.TI_core_16384_3 n hn) fT wT hf hw)
    have h5 := compl_inter_charge h4 (BstLean.Part186.SCovP_ret_charge hn (BstLean.Part186.geoP_4 hn)
      (BstLean.Part186.TI_core_16384_4 n hn) fT wT hf hw)
    have h6 := compl_inter_charge h5 (BstLean.Part186.SCovP_ret_charge hn (BstLean.Part186.geoP_5 hn)
      (BstLean.Part186.TI_core_16384_5 n hn) fT wT hf hw)
    have h7 := compl_inter_charge h6 (BstLean.Part186.SCovP_ret_charge hn (BstLean.Part186.geoP_6 hn)
      (BstLean.Part186.TI_core_16384_6 n hn) fT wT hf hw)
    refine le_trans h7 ?_
    norm_num
  set EA' := EA ∩ S with hEA'
  have hEA'm : MeasurableSet EA' := hEA.inter hSm
  have hA' : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ) ≤
      δA + (5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6) := by
    have hsub : BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ ⊆
        (BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
          BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ∪ Sᶜ := by
      intro c hc
      by_cases h : c ∈ EA
      · right; intro h2; exact hc.2 ⟨h, h2⟩
      · left; exact ⟨hc.1, h⟩
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add hA hSc))
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'
    with hE₁d
  have hE₁ : MeasurableSet E₁ :=
    ((BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)).inter
      hEA'm
  obtain ⟨hW1, hW2⟩ := BstLean.Part159.paper_world hn16 D rfl (fun _ => rfl)
  have hch : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng + (δA + (5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6)) := by
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
  have hFA : FRAME_A_hyp D (1967 / 1000 / n) G :=
    frameA_K_16384 hn D (paperDesign_agentCentre fT wT hf hw) hWin
      (fun c hc => (hFr c hc).1.1.1.1.1.1)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.1.1.1)
      (fun c hc => (hFr c hc).1.1.2)
      (fun c hc => (hFr c hc).1.2)
      (fun c hc => (hFr c hc).2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.2)
      (fun c hc => hc.2.1.2.2.1.2)
      (fun c hc => hc.2.1.2.2.2)
  have hRA' : REPLA_mix_hyp D t hAL G := by
    intro c hc
    refine hRA c ⟨hc.1, ⟨⟨hc.2.1.1, hc.2.1.2.1⟩, hc.2.2⟩⟩
  have hsum : BstLean.Part159.δPap + BstLean.Part159.vPap / hWL ^ 2 +
      (BstLean.Part159.δAng + (δA + (5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6)) + 33515 / 10 ^ 8) ≤ 2559 / 500000 := by
    unfold roomA at hroom
    rw [roomX_eq, BstLean.Part187.roomT16384K_eq] at hroom
    linarith
  exact classifier_frame_16384K hn D t hEv' hsum hFW hFA hRA'

end BstLean.Part183.F16384

namespace BstLean.Part187

/-- **The frame junction at `n ≥ 16 384` with the two-level core** (headline, unconditional). -/
theorem FREE16384K_proved : BstLean.Part183.FREEg_stmt 16384 (-(1845 / 1000000)) :=
  BstLean.Part183.F16384.FREE16384K_proved

end BstLean.Part187

#print axioms BstLean.Part187.FREE16384K_proved
