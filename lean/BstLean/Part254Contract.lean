import BstLean.Part254SharpNetwork

/-! The Part253 statement shape, supplied with larger certified caps. -/
namespace BstLean.Part254
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part169 (paperDesignP)
open BstLean.Part249 (optionBSharp)

theorem localCov_contract :
    ∀ (i : Fin 60) (θ : ℝ), 10 ≤ i.val ∧ i.val ≤ 52 → θ ∈ cell i → ∀ (c : Ret 12225),
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) = θ →
      0 < (paperDesignP 12225).tau0 c →
      c ∈ agentEv (paperDesignP 12225) (optionBSharp 12225) →
      BstLean.Part153.Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP 12225).tau0 c) ≤
        (13 / 10) * (2 / (12225 : ℝ)) / 12225 →
      ∀ v : Fin (mA 12225) → ℝ,
        BstLean.Part182.Dq c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP 12225).tau0 c) v ≤
          capTable i * (2 / (12225 : ℝ)) / 12225 * normSq v := by
  intro i θ _hneeded hi c he hτ hC hX v
  exact localCov i θ hi (paperDesignP 12225) c he hτ hC hX v

/-- No smaller nonnegative billionth-grid number bounds the chosen envelope.
This is not optimality over all covariance proofs. -/
theorem least_grid_envelope_cap (i : Fin 60) (hi : Needed i) (q : ℕ)
    (hq : gaussianEnvelope (cellUpper i) ≤ (q : ℝ) / 10 ^ 9) :
    capTable i ≤ (q : ℝ) / 10 ^ 9 := by
  obtain ⟨p, hp⟩ := capTable_grid i hi
  by_contra h
  have hqp : (q : ℝ) < p := by rw [hp] at h; linarith
  have hqpN : q < p := by exact_mod_cast hqp
  have hs : (q : ℝ) + 1 ≤ p := by exact_mod_cast hqpN
  have hr : (q : ℝ) / 10 ^ 9 ≤ capTable i - 1 / 10 ^ 9 := by rw [hp]; linarith
  exact (not_lt_of_ge (hq.trans hr)) (capTable_certificate i hi).previous

theorem envelope_on_cell (i : Fin 60) {θ : ℝ} (hi : θ ∈ cell i) :
    gaussianEnvelope θ ≤ capTable i := by
  have hθ0 : 0 ≤ θ := by linarith [(cell_window hi).1]
  have hu : cellUpper i ≤ (528 / 1000 : ℝ) :=
    (min_le_right _ _).trans (by norm_num [worldUpper])
  exact (gaussianEnvelope_mono hθ0 hi.2 hu).trans
    (capTable_certificate i (cell_needed hi)).upper

theorem least_grid_cell_cap (i : Fin 60) (hi : Needed i) (q : ℕ)
    (hq : ∀ θ ∈ cell i, gaussianEnvelope θ ≤ (q : ℝ) / 10 ^ 9) :
    capTable i ≤ (q : ℝ) / 10 ^ 9 :=
  least_grid_envelope_cap i hi q (hq _ ⟨cell_nonempty i hi, le_rfl⟩)

theorem certified_cap_gap (i : Fin 60) (hi : Needed i) :
    (BstLean.Part251.rowCellAudit i).covarianceCap < capTable i :=
  (capTable_certificate i hi).source_gap

theorem localCov_of_good (i : Fin 60) (D : Design 12225) (c : Ret 12225)
    (hi : BstLean.Part150.thetaC c.1.2 (D.tau0 c) ∈ cell i)
    (hτ : 0 < D.tau0 c) (hc : c ∈ BstLean.Part249.optionBGood D)
    (v : Fin (mA 12225) → ℝ) :
    BstLean.Part182.Dq c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) v ≤
      capTable i * (2 / (12225 : ℝ)) / 12225 * normSq v :=
  localCov i _ hi D c rfl hτ hc.1 (hc.2 hτ) v

theorem covariance_and_moment_charge (D : Design 12225) (hτW : TauWorld D) :
    (retDist D.toCentres).real (BstLean.Part249.optionBGood D)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part249.optionB_good_charge (by norm_num) D hτW

end BstLean.Part254
