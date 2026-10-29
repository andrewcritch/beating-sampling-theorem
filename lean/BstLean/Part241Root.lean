import BstLean.Part241Pass
import BstLean.Part228Root

/-! The conditional-pass root retains each price and the actual latitude tail. -/
namespace BstLean.Part241
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part228

variable {n : ℕ}

/-- The variable paper split uses the same full conditional location mean. -/
theorem fullF_dPaper (c : Ret n) (wl ws σl η : ℝ) (h0 : 0 < η) (h1 : η < 1) :
    fullF c (BstLean.Part162.dPaper (paperDesignP n) c wl ws σl η h0 h1) = fbR c := rfl

/-- The variable paper split uses the same variance term as the original split. -/
theorem varianceTerm_dPaper (c : Ret n) (wl ws σl η : ℝ) (h0 : 0 < η) (h1 : η < 1) :
    varianceTerm c (BstLean.Part162.dPaper (paperDesignP n) c wl ws σl η h0 h1) = VR c := rfl

/-- These are deterministic moment inputs on one retained value.
This structure contains no event charge or independence premise. -/
structure PassInputs (c : Ret n) (split : SplitData n)
    (χ d ε vmax aw af Hf Cv : ℝ) : Prop where
  he : 0 < eR c
  hd : 1 / 5 ≤ d
  hε1 : ε < 1
  hT : 0 < ε - vmax / d
  haw : 0 < aw
  haf : 0 < af
  hHf : 0 < Hf
  hCv : 0 < Cv
  hSbd : ∀ a ∈ (keptIx (paperDesignP n) c split), 2 / (n : ℝ) * d ≤ split.Sb a
  hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ
  hVm : ∀ a ∈ (keptIx (paperDesignP n) c split), |varianceTerm c split a| ≤ vmax
  iW2 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 2) (keptIx (paperDesignP n) c
    split) (muI n)
  iW6 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 6) (keptIx (paperDesignP n) c
    split) (muI n)
  iW8 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (keptIx (paperDesignP n) c
    split) (muI n)
  iF2 : IntegrableOn (fun a => ((n : ℝ) * (fullF c split a - ftR c a)) ^ 2) (keptIx (paperDesignP n)
    c split) (muI n)
  iF4 : IntegrableOn (fun a => ((n : ℝ) * (fullF c split a - ftR c a)) ^ 4) (keptIx (paperDesignP n)
    c split) (muI n)
  iF8 : IntegrableOn (fun a => ((n : ℝ) * (fullF c split a - ftR c a)) ^ 8) (keptIx (paperDesignP n)
    c split) (muI n)
  if4 : IntegrableOn (fun a => fullF c split a ^ 4) (keptIx (paperDesignP n) c split) (muI n)
  if24 : IntegrableOn (fun a => fullF c split a ^ 24) (keptIx (paperDesignP n) c split) (muI n)
  ifF2 : IntegrableOn (fun a => fullF c split a ^ 2 * ((n : ℝ) * (fullF c split a - ftR c a)) ^ 2)
    (keptIx (paperDesignP n) c split)
      (muI n)
  ifF6 : IntegrableOn (fun a => fullF c split a ^ 6 * ((n : ℝ) * (fullF c split a - ftR c a)) ^ 6)
    (keptIx (paperDesignP n) c split)
      (muI n)
  iV : IntegrableOn (fun a => ((n : ℝ) * varianceTerm c split a) ^ 2) (keptIx (paperDesignP n) c
    split) (muI n)
  hW8 : ∫ a in (keptIx (paperDesignP n) c split), ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^
    8
  hF8 : ∫ a in (keptIx (paperDesignP n) c split), ((n : ℝ) * (fullF c split a - ftR c a)) ^ 8 ∂muI n
    ≤ af ^ 8
  hf4 : ∫ a in (keptIx (paperDesignP n) c split), fullF c split a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in (keptIx (paperDesignP n) c split), fullF c split a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in (keptIx (paperDesignP n) c split), ((n : ℝ) * varianceTerm c split a) ^ 2 ∂muI n ≤ Cv
    ^ 2

/-- The moment inputs supply the bias hypothesis for the stored conditional passes. -/
theorem bias_of_passInputs (hn : 0 < n) (c : Ret n) (split : SplitData n)
    {χ d ε vmax aw af Hf Cv : ℝ} (P : PassInputs c split χ d ε vmax aw af Hf Cv) :
    BIAS_hyp (paperDesignP n) c split (biasRoot n χ d ε vmax aw af Hf Cv) := by
  exact conditional_pass_bias hn c split P.he P.hd P.hε1 P.hT P.haw P.haf P.hHf P.hCv P.hSbd P.hc
    P.hVm P.iW2 P.iW6 P.iW8 P.iF2 P.iF4 P.iF8 P.if4 P.if24 P.ifF2 P.ifF6 P.iV P.hW8 P.hF8 P.hf4
    P.hf24 P.hV

/-- The removal, mixture, displacement, bias and tail roots remain separate. -/
noncomputable def agentRoot (η B hmix Dd hb tail : ℝ) : ℝ :=
  √(2 * (1 + η⁻¹) * B) + hmix + √Dd + hb + tail

/-- A charged fluctuation supply and the pass moments give the replacement root. -/
theorem conditional_pass_root (hn : 2 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hc : c.1.2 ≠ 0)
    {χ d ε vmax aw af Hf Cv hfl tl tu : ℝ}
    (P : PassInputs c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (paperDesignP n) t c split hfl)
    (hT : BulkChernoffDomain (paperDesignP n) c tl tu) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      hfl + biasRoot n χ d ε vmax aw af Hf Cv +
        bulkTailRoot (paperDesignP n) c tl tu := by
  exact repla_root_of_split hn (paperDesignP n) t c hc hT.tau_pos split hF
    (bias_of_passInputs (by omega) c split P)
    (tail_hyp_chernoff (paperDesignP n) c hT)

/-- The mixture root can use a chi-square price or a sharper direct supply.
This theorem places no chi-square restriction on the mixture supply. -/
theorem conditional_pass_root_prices (hn : 2 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hc : c.1.2 ≠ 0)
    {χ d ε vmax aw af Hf Cv B hmix Dd tl tu : ℝ}
    (P : PassInputs c split χ d ε vmax aw af Hf Cv) (hmix0 : 0 ≤ hmix)
    (hB : ∫ a, removed (BstLean.Part29.stdGauss (Fin (n - 1))) split.good a
      ∂muI n ≤ B)
    (hMix : ∫ a in keptIx (paperDesignP n) c split,
      (√(goodMean (BstLean.Part29.stdGauss (Fin (n - 1))) split.good
        (pLat (paperDesignP n) t c) a) - √(q0Lat t c split a)) ^ 2 ∂muI n ≤ hmix ^ 2)
    (hDisp : ∫ a in keptIx (paperDesignP n) c split,
      hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
        (split.S0 a) (split.Sb a) ∂muI n ≤ Dd)
    (hT : BulkChernoffDomain (paperDesignP n) c tl tu) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      agentRoot split.eta B hmix Dd (biasRoot n χ d ε vmax aw af Hf Cv)
        (bulkTailRoot (paperDesignP n) c tl tu) := by
  have hF : FLUCT_hyp (paperDesignP n) t c split
      (√(2 * (1 + split.eta⁻¹) * B) + hmix + √Dd) := by
    refine ⟨B, hmix ^ 2, Dd, hB, hMix, hDisp, ?_⟩
    rw [Real.sqrt_sq hmix0]
  exact conditional_pass_root hn t c split hc P hF hT

/-- A proved tail cap and an explicit arithmetic reserve give the paper root form. -/
theorem root_new (hn : 2 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hc : c.1.2 ≠ 0)
    {χ d ε vmax aw af Hf Cv hfl tl tu tail reserve : ℝ}
    (P : PassInputs c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (paperDesignP n) t c split hfl)
    (hT : BulkChernoffDomain (paperDesignP n) c tl tu)
    (htail : bulkTailRoot (paperDesignP n) c tl tu ≤ tail) (hr : 0 ≤ reserve) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      hfl + biasRoot n χ d ε vmax aw af Hf Cv + tail + reserve := by
  have h := conditional_pass_root hn t c split hc P hF hT
  linarith

/-- The latitude-moment interface and pass moments use the same variable paper split. -/
theorem conditional_pass_root_latMom (hn : 2 ≤ n) (t : ℝ) (c : Ret n)
    (hc : c.1.2 ≠ 0) {wl ws σl η CA χ d ε vmax aw af Hf Cv tl tu : ℝ} {q : ℕ}
    (hwl : 0 < wl) (hws : 0 < ws) (hσl : 0 < σl) (hη0 : 0 < η) (hη1 : η < 1)
    (hcA : 0 < normSq c.2.1.2) (hCA : normSq c.2.1.2 ≤ CA)
    (hε : BstLean.Part162.eps0 ws σl < 1)
    (L : BstLean.Part162.LatMom (paperDesignP n) c σl q)
    (P : PassInputs c (BstLean.Part162.dPaper (paperDesignP n) c wl ws σl η hη0 hη1)
      χ d ε vmax aw af Hf Cv)
    (hT : BulkChernoffDomain (paperDesignP n) c tl tu) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      BstLean.Part162.rootFL wl ws η CA L + biasRoot n χ d ε vmax aw af Hf Cv +
        bulkTailRoot (paperDesignP n) c tl tu := by
  exact replacement_root_latMom hn (paperDesignP n) t c hc hwl hws hσl hη0 hη1
    hcA hCA hε L (bias_of_passInputs (by omega) c _ P) hT

/-- The event junction adds no charge and makes no independence assumption. -/
theorem conditional_pass_root_on_event (hn : 2 ≤ n) (t H : ℝ) {E : Set (Ret n)}
    (h : ∀ c ∈ E, ∃ (split : SplitData n)
      (χ d ε vmax aw af Hf Cv hfl tl tu : ℝ),
      c.1.2 ≠ 0 ∧ PassInputs c split χ d ε vmax aw af Hf Cv ∧
      FLUCT_hyp (paperDesignP n) t c split hfl ∧
      BulkChernoffDomain (paperDesignP n) c tl tu ∧
      hfl + biasRoot n χ d ε vmax aw af Hf Cv +
        bulkTailRoot (paperDesignP n) c tl tu ≤ H) :
    REPLA_mix_hyp (paperDesignP n) t H E := by
  intro c hc
  obtain ⟨split, χ, d, ε, vmax, aw, af, Hf, Cv, hfl, tl, tu, hcentre, P, hF, hT, hsum⟩ := h c hc
  exact (conditional_pass_root hn t c split hcentre P hF hT).trans hsum

end BstLean.Part241
