import BstLean.Part243Agent
import BstLean.Part169Int

/-! Stored-pass inputs for variable paper splits. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

variable {n : ℕ}

/-- The full residual scale inherits the good-input cutoff on every kept index. -/
theorem paper_scale_lower (hn : 1 ≤ n) (c : Ret n)
    {wl ws σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 < η) (hη1 : η < 1)
    {a : Ix n}
    (ha : a ∈ keptIx (paperDesignP n) c
      (BstLean.Part162.dPaper (paperDesignP n) c wl ws σ η hη hη1)) :
    (1 - η) * σ ^ 2 ≤
      (BstLean.Part162.dPaper (paperDesignP n) c wl ws σ η hη hη1).Sb a := by
  let D := BstLean.Part162.dPaper (paperDesignP n) c wl ws σ η hη hη1
  have hk := BstLean.Part162.kept_facts hn (paperDesignP n) c hη hη1 ha
  have ms : MeasurableSet (slice D a) := measurableSet_slice _ _
  have hi := integral_mono ((integrable_const (σ ^ 2)).indicator ms)
    (integrable_sA hn (paperDesignP n) c a) (fun v => show
      (slice D a).indicator (fun _ => σ ^ 2) v ≤ sA (paperDesignP n) c a v from by
      by_cases hv : v ∈ slice D a
      · rw [Set.indicator_of_mem hv]
        exact pow_le_pow_left₀ hσ (hk.2.2.2.2.1 v hv).2 2
      · rw [Set.indicator_of_notMem hv]
        change 0 ≤ BstLean.Part162.sgA (paperDesignP n) c a v ^ 2
        positivity)
  rw [integral_indicator ms, integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ] at hi
  exact (mul_le_mul_of_nonneg_right hk.2.1 (sq_nonneg σ)).trans hi

/-- These six numerical moment bounds use the actual stored tables and the selected kept set.
All integrability fields are supplied below. -/
structure PaperMoments (c : Ret n) (K : Set (Ix n)) (vmax aw af Hf Cv : ℝ) : Prop where
  variance : ∀ a ∈ K, |VR c a| ≤ vmax
  energyError : ∫ a in K, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8
  locationError : ∫ a in K, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8
  location4 : ∫ a in K, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  location24 : ∫ a in K, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  variance2 : ∫ a in K, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2

/-- Supply every integrability field for a variable split, with no event payment. -/
theorem passInputs_of_paperMoments (hn : 1 ≤ n) (c : Ret n)
    {wl ws σ η χ d ε vmax aw af Hf Cv : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hσ : 0 ≤ σ)
    (he : 0 < eR c) (hd : 1 / 5 ≤ d) (hε : ε < 1)
    (hT : 0 < ε - vmax / d) (haw : 0 < aw) (haf : 0 < af)
    (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hfloor : 2 / (n : ℝ) * d ≤ (1 - η) * σ ^ 2)
    (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (P : PaperMoments c (keptIx (paperDesignP n) c
      (BstLean.Part162.dPaper (paperDesignP n) c wl ws σ η hη hη1)) vmax aw af Hf Cv) :
    BstLean.Part241.PassInputs c
      (BstLean.Part162.dPaper (paperDesignP n) c wl ws σ η hη hη1)
      χ d ε vmax aw af Hf Cv := by
  obtain ⟨Mf, hf⟩ := bdd_fbR hn c
  obtain ⟨Mw, hw⟩ := bdd_wbR hn c
  obtain ⟨Nf, hf'⟩ := bdd_ftR hn c
  obtain ⟨Nw, hw'⟩ := bdd_wtR hn c
  obtain ⟨MV, hV⟩ := bdd_VR hn c
  have mf := measurable_fbR c
  have mV := measurable_VR c
  have mW := ((measurable_wbR c).sub (measurable_wtR c)).const_mul (n : ℝ)
  have mF := (mf.sub (measurable_ftR c)).const_mul (n : ℝ)
  have bW := bdd_nsub hw hw'
  have bF := bdd_nsub hf hf'
  refine ⟨he, hd, hε, hT, haw, haf, hHf, hCv,
    (fun a ha => hfloor.trans (paper_scale_lower hn c hσ hη hη1 ha)), hc, ?_,
    intOn_of_bdd (mW.pow_const 2) (bdd_pow bW 2) _,
    intOn_of_bdd (mW.pow_const 6) (bdd_pow bW 6) _,
    intOn_of_bdd (mW.pow_const 8) (bdd_pow bW 8) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    P.energyError, ?_, ?_, ?_, ?_⟩
  all_goals simp only [BstLean.Part241.fullF_dPaper, BstLean.Part241.varianceTerm_dPaper]
  · exact P.variance
  · exact intOn_of_bdd (mF.pow_const 2) (bdd_pow bF 2) _
  · exact intOn_of_bdd (mF.pow_const 4) (bdd_pow bF 4) _
  · exact intOn_of_bdd (mF.pow_const 8) (bdd_pow bF 8) _
  · exact intOn_of_bdd (mf.pow_const 4) (bdd_pow hf 4) _
  · exact intOn_of_bdd (mf.pow_const 24) (bdd_pow hf 24) _
  · exact intOn_of_bdd ((mf.pow_const 2).mul (mF.pow_const 2))
      (bdd_mul (bdd_pow hf 2) (bdd_pow bF 2)) _
  · exact intOn_of_bdd ((mf.pow_const 6).mul (mF.pow_const 6))
      (bdd_mul (bdd_pow hf 6) (bdd_pow bF 6)) _
  · exact intOn_of_bdd ((mV.const_mul _).pow_const 2) (bdd_pow (bdd_nmul hV) 2) _
  · exact P.locationError
  · exact P.location4
  · exact P.location24
  · exact P.variance2

end BstLean.Part252
