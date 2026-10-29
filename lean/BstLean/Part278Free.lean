import BstLean.Part278Family
import BstLean.Part163Bias

/-!
# Part 278 (O5, the replacement layer for n ≥ 23 000)

`classifier_free23_fluct_st` is the stated-design form of
`Part163.classifier_paper_free23_fluct` at the paper tables. Its premise `hFl` (FLUCT and BIAS) is
for `paperDesignP n`. Its premise `hodd` (odd root `≤ 10⁻²⁰`) is on the same good set. Its
conclusion is for `progOut (statedDesign n)`. The proof spends the reserve `10⁻²⁰`: the paper root
is `≤ 0.006583` (`repla_root_of_split` with `tail_root_num`), and `repla_transfer` adds `10⁻²⁰`.
The good sets of the two designs are the same set, because the events read only the centres and
`τ₀`.
-/

namespace BstLean.Part278

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part160 BstLean.Part169
open BstLean.Part161 (FLUCT_chi_hyp BIAS_hyp SplitData)
open BstLean.Part272 (statedDesign passFSt passWSt measurable_passFSt measurable_passWSt)

theorem classifier_free23_fluct_st {n : ℕ} (hn : 23000 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part163.roomA)
    (hFl : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ BstLean.Part163.Eframe (paperDesignP n))
        (HbarW (paperDesignP n)) hWL,
      ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
        FLUCT_chi_hyp (paperDesignP n) c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧
        BIAS_hyp (paperDesignP n) c d (4295 / 10 ^ 6))
    (hodd : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ BstLean.Part163.Eframe (paperDesignP n))
        (HbarW (paperDesignP n)) hWL,
      |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (statedDesign n) t aL (10 ^ 12) x.1 x.2)} := by
  have h0 : REPLA_mix_hyp (paperDesignP n) t (6583 / 10 ^ 6)
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ BstLean.Part163.Eframe (paperDesignP n))
        (HbarW (paperDesignP n)) hWL) := by
    intro c hc
    obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hFl c hc
    have hwc : BstLean.Part161.WINDOW (paperDesignP n) c :=
      BstLean.Part161.window_paper (by omega) passF passW measurable_passF measurable_passW
        hc.1.1 hc.2.1.1.1 hc.2.1.1.2
    have h := BstLean.Part161.repla_root_of_split (by omega) (paperDesignP n) t c hwc.1 hwc.2.1 d
      (BstLean.Part161.fluct_of_chi (paperDesignP n) t c d hF) hB
      (BstLean.Part161.tail_of_window (by omega) (paperDesignP n) c hwc)
    have ht := BstLean.Part161.tail_root_num
    linarith
  have h1 := repla_transfer (D := paperDesignP n) (D' := statedDesign n)
    (fun c => QStand_st t c) h0 hodd
  have hRA : REPLA_mix_hyp (paperDesign n passFSt passWSt measurable_passFSt measurable_passWSt)
      t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩
          BstLean.Part163.Eframe (paperDesign n passFSt passWSt measurable_passFSt
            measurable_passWSt))
        (HbarW (paperDesign n passFSt passWSt measurable_passFSt measurable_passWSt)) hWL) := by
    unfold hAL
    exact h1
  exact BstLean.Part163.classifier_paper_free23 hn passFSt passWSt measurable_passFSt
    measurable_passWSt t hEA hA hroom hRA

end BstLean.Part278
