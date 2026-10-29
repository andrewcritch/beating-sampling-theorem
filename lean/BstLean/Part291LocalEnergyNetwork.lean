import BstLean.Part291AgentCentre

namespace BstLean.BlueprintLow
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part188 BstLean.Part206 BstLean.Part211

theorem agentLocalEnergyBand {n : ℕ} (hn : LowBand n) {c : Ret n} {lo E : ℝ}
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.472 : ℝ) 0.528)
    (hlo : lo ≤ BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c))
    (hτ : 0 < (paperDesignP n).tau0 c)
    (hC : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c))
    (hE : ∀ q : ℝ, 0 ≤ q → q ≤ 1 - lo →
      energyRatio n (gMinus n) q ≤ 1 ∧
      energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ E) :
    centreEnergy (paperDesignP n) c ≤ E := by
  have hn8 := hn.1
  let θ := BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c)
  have hθ : θ ∈ Icc (0.46 : ℝ) 0.528 := ⟨by linarith [hw.1], hw.2⟩
  have C := agentCentreCertificate hn
  have hQ := hE (1 - θ) (by dsimp [θ]; linarith [hw.2]) (by dsimp [θ]; linarith)
  have h := computed_energy_on_source (by omega : 2 ≤ n) (by omega : 1 ≤ n)
    c.1.2 hτ (by norm_num : (0 : ℝ) ≤ 0.011)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hθ.2], by linarith [hθ.1]⟩)
    (le_refl (1 - θ)) C.energy_root C.energy_upper hQ.1
    (C.lower_root θ hθ) (C.lower_bracket θ hθ) (C.lower_guard θ hθ) hC.1.1.1.1
  rw [BstLean.Part222.energy_normalization (by omega) (paperDesignP n) c hτ
    (BstLean.Part263.paper_centre_eq c)]
  apply h.2.trans
  convert hQ.2 using 1 <;> norm_num

end BstLean.BlueprintLow
