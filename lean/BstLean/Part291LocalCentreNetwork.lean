import BstLean.Part291LocalCentreWitness
import BstLean.Part291SourceEvents
import BstLean.Part263Source

namespace BstLean.BlueprintLow
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169 BstLean.Part211

/-- The same centre event supplies every local full-centre cap. Selecting a
noise interval does not introduce an event union. -/
theorem agentLocalCentreBand {n : ℕ} (hn : LowBand n) {c : Ret n}
    {Θ full : ℝ} (hΘ : Θ ∈ Icc (0.46 : ℝ) 0.54)
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.46 : ℝ) Θ)
    (hc : 0 < normSq c.1.2) (hτ : 0 < (paperDesignP n).tau0 c)
    (h : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c))
    (hfull : fullFormula n n 0.011 1.25 1.14 0.46 Θ (0.004172 + 0.34 * Θ) 1.269 ≤ full) :
    CENTRE_at (paperDesignP n) c full := by
  have hn8 := hn.1
  have hnhi := hn.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ : ENNReal.ofReal (1 / 20000 : ℝ) ≠ 0 := by norm_num
  have F := agentCentreEvent_sources hc hτ h
  have hop : BstLean.Part219.operatorAllowance c.1.2 ((paperDesignP n).tau0 c)
      0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ 1.269 := by
    convert BstLean.Part277.operator_allowance_8000 hn.1 c.1.2 hτ using 1 <;> norm_num
  have hsource := BstLean.Part222.centreSource_on_operator_event c.1.2
    ((paperDesignP n).tau0 c) 0.006 1.269 hδ F.base_event F.operator_event
    (BstLean.Part222.operatorXiAllowance_le c.1.2 ((paperDesignP n).tau0 c) 0.006 1.269 _ hop)
  have hb := full_error_on_source (by omega) (by omega) (by omega : 1 ≤ n)
    c.1.2 hc hτ (by norm_num : (0 : ℝ) ≤ 1.269) (fun _ => 0.006)
    (localMomentCertificate hn hΘ) hw.1 hw.2
    (BstLean.Part277.energy_root_guard_8000 hn.1).le
    (by have := BstLean.Part277.gMinus_ge_989 hn.1; linarith)
    (by have := BstLean.Part277.gPlus_le_1011 hn.1; linarith) hsource.1
  have hraw : fullError (J := n) c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP n).tau0 c) ≤
      fullFormula n n 0.011 1.25 1.14 0.46 Θ (0.004172 + 0.34 * Θ) 1.269 := by
    unfold fullError BstLean.Part211.hiddenCentre
    apply (div_le_iff₀ (by positivity : 0 < 2 / (n : ℝ) / n)).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hb
  have hh := hraw.trans hfull
  rw [BstLean.Part222.fullError_normalization (by omega) (paperDesignP n) c
    (BstLean.Part263.paper_centre_eq c)] at hh
  exact BstLean.Part222.centre_at_of_raw_bound (paperDesignP n) c hh

end BstLean.BlueprintLow
