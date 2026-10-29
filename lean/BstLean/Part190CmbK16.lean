import BstLean.Part188All
import BstLean.Part184Def
import BstLean.Part190FrK16
import BstLean.Part190LedK16
import BstLean.Part190GeoP
import BstLean.Part190TC
import BstLean.Part190T7
import BstLean.Part188R159Uncond
import BstLean.Part188R159Win
import BstLean.Part188R163Comb
import BstLean.Part190GCov
import BstLean.Part190CovC
import BstLean.Part186GeoP
import BstLean.Part186TC
import BstLean.Part186T7
import BstLean.Part181Comb



namespace BstLean.Part190
open BstLean.Part188
open BstLean.Part187
open BstLean.Part187


noncomputable def roomT16200K : ℝ := -(2212 / 1000000)

lemma roomT16200K_eq : roomT16200K = -(2212 / 1000000) := rfl

end BstLean.Part190

namespace BstLean.Part190.Frame16200
open BstLean.Part183 BstLean.Part183.F16250

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181
open BstLean.Part163 (Eframe roomA events_with_Eframe)

variable {n : ℕ}

lemma compl_inter_charge {μ : Measure (Ret n)} [IsFiniteMeasure μ] {A B : Set (Ret n)} {a b : ℝ}
    (hA : μ.real Aᶜ ≤ a) (hB : μ.real Bᶜ ≤ b) : μ.real (A ∩ B)ᶜ ≤ a + b := by
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans (add_le_add hA hB)


theorem FREE16200K_proved : BstLean.Part183.FREEg_stmt 16200 BstLean.Part190.roomT16200K := by
  intro n hn fT wT hf hw t EA hEA δA hA hroom hRA
  have hgeo := geoT16200_holds hn
  have hTIn := BstLean.Part190.TI_two_16200 n hn
  have hn16 : 16200 ≤ n := hn
  set D := paperDesign n fT wT hf hw with hDd
  set S := (agentEv D (SXM16200 n) ∩ agentEv D (SCovT16200 n) ∩ agentEv D (BstLean.Part186.SCovP n (46 / 100) (47 / 100) (78 / 125)) ∩ agentEv D (BstLean.Part186.SCovP n (47 / 100) (48 / 100) (309 / 500)) ∩ agentEv D (BstLean.Part186.SCovP n (48 / 100) (49 / 100) (613 / 1000)) ∩ agentEv D (BstLean.Part186.SCovP n (49 / 100) (50 / 100) (76 / 125)) ∩ agentEv D (BstLean.Part186.SCovP n (50 / 100) (51 / 100) (603 / 1000)) ∩ agentEv D (BstLean.Part186.SCovP n (51 / 100) (52 / 100) (299 / 500)) ∩ agentEv D (BstLean.Part186.SCovP n (52 / 100) (528 / 1000) (593 / 1000))) ∩ agentEv D (BstLean.Part188.Sc.SSc97 n) with hSd
  have mP : ∀ a b l : ℝ, MeasurableSet (agentEv D (BstLean.Part186.SCovP n a b l)) :=
    fun a b l => measurableSet_agentEv D (BstLean.Part186.measurableSet_SCovP n a b l)
  have hSm : MeasurableSet S :=
    (((((((((measurableSet_agentEv D (measurableSet_SXM16200 n)).inter
      (measurableSet_agentEv D (measurableSet_SCovT16200 n))).inter (mP _ _ _)).inter (mP _ _ _)).inter
      (mP _ _ _)).inter (mP _ _ _)).inter (mP _ _ _)).inter (mP _ _ _)).inter (mP _ _ _)).inter
      (measurableSet_agentEv D (BstLean.Part188.Sc.measurableSet_SSc97 n))
  have hSc : (retDist (paperCentres n)).real Sᶜ ≤ 5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6 + 41 / 1000000 := by
    have h0 := compl_inter_charge (SXM16200_ret_charge hn fT wT hf hw)
      (SCovT16200_ret_charge hn hgeo hTIn fT wT hf hw)
    have h1 := compl_inter_charge h0 (BstLean.Part190.Core.SCovP_ret_charge hn (BstLean.Part190.geoP16200_0 hn)
      (BstLean.Part190.TI_core_16200_0 n hn) fT wT hf hw)
    have h2 := compl_inter_charge h1 (BstLean.Part190.Core.SCovP_ret_charge hn (BstLean.Part190.geoP16200_1 hn)
      (BstLean.Part190.TI_core_16200_1 n hn) fT wT hf hw)
    have h3 := compl_inter_charge h2 (BstLean.Part190.Core.SCovP_ret_charge hn (BstLean.Part190.geoP16200_2 hn)
      (BstLean.Part190.TI_core_16200_2 n hn) fT wT hf hw)
    have h4 := compl_inter_charge h3 (BstLean.Part190.Core.SCovP_ret_charge hn (BstLean.Part190.geoP16200_3 hn)
      (BstLean.Part190.TI_core_16200_3 n hn) fT wT hf hw)
    have h5 := compl_inter_charge h4 (BstLean.Part190.Core.SCovP_ret_charge hn (BstLean.Part190.geoP16200_4 hn)
      (BstLean.Part190.TI_core_16200_4 n hn) fT wT hf hw)
    have h6 := compl_inter_charge h5 (BstLean.Part190.Core.SCovP_ret_charge hn (BstLean.Part190.geoP16200_5 hn)
      (BstLean.Part190.TI_core_16200_5 n hn) fT wT hf hw)
    have h7 := compl_inter_charge h6 (BstLean.Part190.Core.SCovP_ret_charge hn (BstLean.Part190.geoP16200_6 hn)
      (BstLean.Part190.TI_core_16200_6 n hn) fT wT hf hw)
    have h8 := compl_inter_charge h7 (BstLean.Part188.Sc.SSc97_ret_charge hn fT wT hf hw)
    refine le_trans h8 ?_
    norm_num
  set EA' := EA ∩ S with hEA'
  have hEA'm : MeasurableSet EA' := hEA.inter hSm
  have hA' : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA'ᶜ) ≤
      δA + (5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6 + 41 / 1000000) := by
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
  obtain ⟨hW1, hW2⟩ := BstLean.Part188.Base159_R.paper_world hn16 D rfl (fun _ => rfl)
  have hch : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng + (δA + (5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6 + 41 / 1000000)) := by
    have h := BstLean.Part188.Base159_R.extra_angle hn16 (paperCentres n) (BstLean.Part159.HP n) EA'
    exact h.trans (add_le_add le_rfl hA')
  have hEv := hW1 hE₁ hch
  have hEv' := BstLean.Part188.Base163_R.events_with_Eframe hn16 D (paperDesign_tauWorld fT wT hf hw) hEv
  set G := goodSet (BstLean.Part159.HP n) (E₁ ∩ Eframe D) (HbarW D) hWL with hGd
  have hWin : ∀ c ∈ G, 0 < D.tau0 c ∧ 46 / 100 ≤ thetaC c.1.2 (D.tau0 c) ∧
      thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000 := by
    intro c hc
    obtain ⟨hτ, -, -, -, h1, h2⟩ := BstLean.Part188.Base159_R.theta_window_paper' hn16 D rfl (fun _ => rfl)
      hc.1.1
    have e := BstLean.Part160.thetaIn_eq D c
    have hm : c ∈ BstLean.Part159.Ethm (paperCentres n) := hc.2.1.1.1
    have hp : c ∈ BstLean.Part159.Ethp (paperCentres n) := hc.2.1.1.2
    refine ⟨hτ, ?_, ?_⟩
    · have := h1 hm; rw [e] at this; linarith
    · have := h2 hp; rw [e] at this; exact this
  have hFW := hW2 (E := G) (fun c hc => hc.1.1)
  have hFr : ∀ c ∈ G, c ∈ Eframe D := fun c hc => hc.2.2
  have hFA : FRAME_A_hyp D (193 / 100 / n) G :=
    frameA_K_16200 hn D (paperDesign_agentCentre fT wT hf hw) hWin
      (fun c hc => (hFr c hc).1.1.1.1.1.1)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.1.1.1.1)
      (fun c hc => hc.2.1.2.2.2)
      (fun c hc => (hFr c hc).1.2)
      (fun c hc => (hFr c hc).2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.1.2)
      (fun c hc => hc.2.1.2.2.1.1.2)
      (fun c hc => hc.2.1.2.2.1.2)
  have hRA' : REPLA_mix_hyp D t hAL G := by
    intro c hc
    refine hRA c ⟨hc.1, ⟨⟨hc.2.1.1, hc.2.1.2.1⟩, hc.2.2⟩⟩
  have hsum : BstLean.Part188.Base159_R.δPap + BstLean.Part188.Base159_R.vPap / hWL ^ 2 +
      (BstLean.Part159.δAng + (δA + (5 / 100000 + 1 / 10 ^ 5 + 7 / 10 ^ 6 + 41 / 1000000)) + 33515 / 10 ^ 8) ≤ 5111 / 1000000 := by
    unfold roomA at hroom
    rw [roomX_eq, BstLean.Part190.roomT16200K_eq] at hroom
    have e1 : BstLean.Part188.Base159_R.δPap = BstLean.Part159.δPap + 1714 / 10 ^ 8 := by
      unfold BstLean.Part188.Base159_R.δPap BstLean.Part159.δPap; norm_num
    have e2 : BstLean.Part188.Base159_R.vPap / hWL ^ 2 = BstLean.Part159.vPap / hWL ^ 2 + 26 / 10 ^ 11 / hWL ^ 2 := by
      unfold BstLean.Part188.Base159_R.vPap BstLean.Part159.vPap; ring
    have e3 : (26 / 10 ^ 11 : ℝ) / hWL ^ 2 ≤ 45 / 10 ^ 6 := by unfold hWL; norm_num
    linarith
  exact classifier_frame_16200K16 hn D t hEv' hsum hFW hFA hRA'

end BstLean.Part190.Frame16200

namespace BstLean.Part190
open BstLean.Part188


theorem FREE16200K_proved : BstLean.Part183.FREEg_stmt 16200 (-(2212 / 1000000)) :=
  BstLean.Part190.Frame16200.FREE16200K_proved

end BstLean.Part190

#print axioms BstLean.Part190.FREE16200K_proved
