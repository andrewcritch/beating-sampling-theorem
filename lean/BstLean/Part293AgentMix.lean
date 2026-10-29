import BstLean.Part293AgentInputs
import BstLean.Part293LowAdapter
import BstLean.Part242MixturePass
import BstLean.Part289Pass

/-! The actual Part291 conditional fields supply the original mixture integrals. -/
namespace BstLean.Part293
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242 BstLean.Part289 BstLean.BlueprintLow

theorem mixture_of_agentSupply {n : ℕ} (hn : 8000 ≤ n) (t : ℝ) (c : Ret n)
    (S : AgentSupplyInputs c) :
    ∫ a in keptIx (idealDesignFloor n (scaleFloor n)) c (lowPaperSplit (paperDesignP n) c),
      (√(goodMean (stdGauss (Fin (n - 1))) (lowPaperSplit (paperDesignP n) c).good
        (pLat (idealDesignFloor n (scaleFloor n)) t c) a) -
        √(q0Lat t c (lowPaperSplit (paperDesignP n) c) a)) ^ 2 ∂muI n ≤
      Envelope.chi2 (1 / n) / 4 +
        6 * mixL3 n (Envelope.eps (1 / n)) (Envelope.A (1 / n)) (Envelope.D (1 / n)) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨heps0, heps1, _, hwin, hcent⟩ := S.split
  obtain ⟨_, hv, _, hw⟩ := S.conditional_norms
  have h := mixture_price_SY2 (paperDesignP n) t c (lowPaperSplit (paperDesignP n) c)
    heps0 heps1
    (show 0 ≤ 2 * (lowMixtureWidth n / √(eR c)) from by
      have := (lowMixtureWidth_bound hn).1.le
      positivity)
    (lowMixtureA_pos hn) (lowMixtureD_pos hn)
    (fun a ha => (show (0 : ℝ) < (2 / n) * 0.18 by positivity).trans_le (hwin a ha).1)
    (fun a ha v hv => ⟨((hwin a ha).2 v hv).1, ((hwin a ha).2 v hv).2.1⟩)
    hcent hv hw S.comparisons.chi_integrable S.comparisons.chi_bound
  rw [actual_lowQ_normalized hn, actual_lowEpsilon_normalized hn,
    actual_lowA_normalized hn, actual_lowD_normalized hn] at h
  exact h

theorem removal_of_agentSupply {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (S : AgentSupplyInputs c) :
    ∫ a, removed (stdGauss (Fin (n - 1))) (lowPaperSplit (paperDesignP n) c).good a
      ∂muI n ≤ Envelope.B (1 / n) := by
  rw [← actual_lowB_normalized hn]
  exact S.comparisons.removal_bound

theorem displacement_of_agentSupply {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (S : AgentSupplyInputs c) :
    ∫ a in keptIx (idealDesignFloor n (scaleFloor n)) c (lowPaperSplit (paperDesignP n) c),
      hellG2 n (((lowPaperSplit (paperDesignP n) c).lam0 a -
        (lowPaperSplit (paperDesignP n) c).lamb a) ^ 2 * normSq c.2.1.2)
        ((lowPaperSplit (paperDesignP n) c).S0 a) ((lowPaperSplit (paperDesignP n) c).Sb a)
      ∂muI n ≤ Envelope.Dd (1 / n) := by
  rw [← actual_lowDisplacement_normalized hn]
  exact S.comparisons.displacement_bound

end BstLean.Part293
