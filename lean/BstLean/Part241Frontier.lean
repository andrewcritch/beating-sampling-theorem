import BstLean.Part241Root
import BstLean.Part228Scale

/-! The checked latitude-tail cap gives the paper's root from dimension 8000. -/
namespace BstLean.Part241
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part228

variable {n : ℕ}

/-- The actual tail root retains its value and its proved cap. -/
theorem conditional_pass_root_frontier (hn : 8000 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hW : WINDOW (paperDesignP n) c)
    {χ d ε vmax aw af Hf Cv hfl : ℝ}
    (P : PassInputs c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (paperDesignP n) t c split hfl) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      hfl + biasRoot n χ d ε vmax aw af Hf Cv + frontierTailRoot (paperDesignP n) c ∧
    frontierTailRoot (paperDesignP n) c < 1 / 10 ^ 8 := by
  exact ⟨conditional_pass_root (by omega) t c split hW.1 P hF
    (bulk_domain_explicit (by omega) (paperDesignP n) c hW),
    frontierTailRoot_lt hn (paperDesignP n) c hW⟩

/-- The paper root uses the certified tail cap and an explicit arithmetic reserve.
The split retains its removal tolerance. The bias floor is a separate parameter. -/
theorem root_new_8000 (hn : 8000 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hW : WINDOW (paperDesignP n) c)
    {χ d ε vmax aw af Hf Cv B hmix Dd : ℝ}
    (P : PassInputs c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (paperDesignP n) t c split
      (√(2 * (1 + split.eta⁻¹) * B) + hmix + √Dd)) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      √(2 * (1 + split.eta⁻¹) * B) + hmix + √Dd +
        biasRoot n χ d ε vmax aw af Hf Cv + 1 / 10 ^ 8 + 1 / 10 ^ 20 := by
  obtain ⟨hroot, htail⟩ := conditional_pass_root_frontier hn t c split hW P hF
  have hr : (0 : ℝ) ≤ 1 / 10 ^ 20 := by positivity
  linarith

/-- Select each parameter package on its retained event without an extra event charge. -/
theorem root_new_8000_on_event (hn : 8000 ≤ n) (t H : ℝ) {E : Set (Ret n)}
    (h : ∀ c ∈ E, ∃ (split : SplitData n) (χ d ε vmax aw af Hf Cv B hmix Dd : ℝ),
      WINDOW (paperDesignP n) c ∧ PassInputs c split χ d ε vmax aw af Hf Cv ∧
      FLUCT_hyp (paperDesignP n) t c split
        (√(2 * (1 + split.eta⁻¹) * B) + hmix + √Dd) ∧
      √(2 * (1 + split.eta⁻¹) * B) + hmix + √Dd +
        biasRoot n χ d ε vmax aw af Hf Cv + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ H) :
    REPLA_mix_hyp (paperDesignP n) t H E := by
  intro c hc
  obtain ⟨split, χ, d, ε, vmax, aw, af, Hf, Cv, B, hmix, Dd, hW, P, hF, hsum⟩ := h c hc
  exact (root_new_8000 hn t c split hW P hF).trans hsum

/-- The integrated removal, mixture and displacement bounds supply the paper root directly. -/
theorem root_new_8000_prices (hn : 8000 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hW : WINDOW (paperDesignP n) c)
    {χ d ε vmax aw af Hf Cv B hmix Dd : ℝ}
    (P : PassInputs c split χ d ε vmax aw af Hf Cv) (hmix0 : 0 ≤ hmix)
    (hB : ∫ a, removed (BstLean.Part29.stdGauss (Fin (n - 1))) split.good a
      ∂muI n ≤ B)
    (hMix : ∫ a in keptIx (paperDesignP n) c split,
      (√(goodMean (BstLean.Part29.stdGauss (Fin (n - 1))) split.good
        (pLat (paperDesignP n) t c) a) - √(q0Lat t c split a)) ^ 2 ∂muI n ≤ hmix ^ 2)
    (hDisp : ∫ a in keptIx (paperDesignP n) c split,
      hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
        (split.S0 a) (split.Sb a) ∂muI n ≤ Dd) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      agentRoot split.eta B hmix Dd (biasRoot n χ d ε vmax aw af Hf Cv)
        (1 / 10 ^ 8) + 1 / 10 ^ 20 := by
  have h := conditional_pass_root_prices (by omega) t c split hW.1 P hmix0 hB hMix hDisp
    (bulk_domain_explicit (by omega) (paperDesignP n) c hW)
  have ht := frontierTailRoot_lt hn (paperDesignP n) c hW
  change _ ≤ agentRoot split.eta B hmix Dd (biasRoot n χ d ε vmax aw af Hf Cv)
    (frontierTailRoot (paperDesignP n) c) at h
  unfold agentRoot at h ⊢
  have hr : (0 : ℝ) ≤ 1 / 10 ^ 20 := by positivity
  linarith

end BstLean.Part241
