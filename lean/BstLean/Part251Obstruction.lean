import BstLean.Part249Bridge
import BstLean.Part249Obstruction

/-! Lower bounds on the certificate expression in Part249.FrameInputs.
These are not lower bounds on the actual network covariance or frame. -/
namespace BstLean.Part251
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part188
open BstLean.Part199 BstLean.Part238

noncomputable def fixedCore : ℝ :=
  min (sharpK (595 / 1000) (35 / 1000) (25 / 100) (51 / 100))
    (BstLean.Part182.ta_lam (595 / 1000) (35 / 1000) (25 / 100))

noncomputable def fixedCovariance (n : ℕ) (θ : ℝ) : ℝ :=
  sharpScalar n θ exampleWide exampleCore fixedCore (67 / 100)
    (1 - 4 * θ / n)⁻¹ (13 / 10)
    (2 * exp (-exampleWide.pair ^ 2 / 2) +
      2 * (BstLean.Part249.optionBDelta n / (1 / 4000)))

theorem fixedCore_lower : (598 / 1000 : ℝ) ≤ fixedCore := by
  apply le_min
  · unfold sharpK
    have := sqrt_nonneg (51 / 100 : ℝ)
    nlinarith
  · unfold BstLean.Part182.ta_lam
    have h := Real.sq_sqrt (show (0 : ℝ) ≤
      ((595 / 1000 - 25 / 100) / 2) ^ 2 + (35 / 1000) ^ 2 by norm_num)
    have h0 := sqrt_nonneg (((595 / 1000 - 25 / 100) / 2) ^ 2 + (35 / 1000 : ℝ) ^ 2)
    nlinarith

theorem fixedCovariance_lower {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Icc (46 / 100) (528 / 1000)) :
    (598 / 1000 : ℝ) * θ ≤ fixedCovariance n θ := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hθ0 : 0 ≤ θ := by linarith [hθ.1]
  have hd : 0 < 1 - 4 * θ / (n : ℝ) := by
    have : 4 * θ / (n : ℝ) < 1 :=
      (div_lt_one (by linarith)).mpr (by linarith [hθ.2])
    linarith
  have he : (1 : ℝ) ≤ (1 - 4 * θ / (n : ℝ))⁻¹ := by
    apply (one_le_inv₀ hd).mpr
    have : 0 ≤ 4 * θ / (n : ℝ) := by positivity
    simpa using (show 1 - 4 * θ / (n : ℝ) ≤ 1 by linarith)
  have hk0 : 0 ≤ fixedCore := (by norm_num : (0 : ℝ) ≤ 598 / 1000).trans fixedCore_lower
  have hk : (598 / 1000 : ℝ) ≤ fixedCore * (1 - 4 * θ / (n : ℝ))⁻¹ :=
    fixedCore_lower.trans (by nlinarith)
  have hr0 := (BstLean.Part235.wide_radius_caps hn hθ.1 hθ.2).1
  have hr1 := (BstLean.Part235.core_radius_caps hn hθ.1 hθ.2).1
  have hi0 : 0 ≤ (1 - radiusMinus n θ exampleWide)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : 0 ≤ (1 - radiusMinus n θ exampleCore)⁻¹ := inv_nonneg.mpr (by linarith)
  have hp : 0 ≤ pairRowBound exampleCore := by unfold pairRowBound; positivity
  have ho : 0 ≤ outsideBound exampleCore := by unfold outsideBound; positivity
  have hs1 : 0 ≤ (67 / 100 : ℝ) * (1 - radiusMinus n θ exampleCore)⁻¹ *
      pairRowBound exampleCore := by positivity
  have hs0 : 0 ≤ (67 / 100 : ℝ) * (1 - radiusMinus n θ exampleWide)⁻¹ *
      outsideBound exampleCore := by positivity
  have hm := mul_le_mul_of_nonneg_left (show (598 / 1000 : ℝ) ≤
    fixedCore * (1 - 4 * θ / (n : ℝ))⁻¹ +
      67 / 100 * (1 - radiusMinus n θ exampleCore)⁻¹ * pairRowBound exampleCore +
      67 / 100 * (1 - radiusMinus n θ exampleWide)⁻¹ * outsideBound exampleCore by linarith) hθ0
  unfold fixedCovariance sharpScalar
  have hb : 0 ≤ (13 / 10 : ℝ) *
    (2 * √(√(2 * exp (-exampleWide.pair ^ 2 / 2) +
      2 * (BstLean.Part249.optionBDelta n / (1 / 4000)))) + √(outsideBound exampleWide)) :=
    by positivity
  nlinarith

theorem frameInputs_covariance_lower {n : ℕ} (hn : 11883 ≤ n)
    {c : Ret n} {cf : ℝ} (F : BstLean.Part249.FrameInputs n c cf) :
    (598 / 1000 : ℝ) *
      BstLean.Part150.thetaC c.1.2 ((BstLean.Part169.paperDesignP n).tau0 c) ≤ F.N :=
  (fixedCovariance_lower hn F.window).trans F.covariance_scalar

theorem massBound_nonneg (n : ℕ) (M H xi E u d : ℝ) :
    0 ≤ BstLean.Part222.massBound n M H xi E u d := by
  unfold BstLean.Part222.massBound
  positivity

theorem frameInputs_beta_nonneg {n : ℕ} {c : Ret n} {cf : ℝ}
    (F : BstLean.Part249.FrameInputs n c cf) : 0 ≤ F.beta :=
  (massBound_nonneg n F.M F.H F.xiP F.E F.u F.d).trans F.mass_scalar

/-- Even a zero mass allowance cannot repair the prescribed cutoff with this
centre allowance. All direction, energy and gap parameters remain arbitrary. -/
theorem no_frameInputs_at_stored_cutoff {c : Ret 12225}
    (F : BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame)
    (hd : F.d ≤ BstLean.Part249.storedFrameCutoff)
    (hxi : (8454 / 100000 : ℝ) ≤ F.xiF) : False := by
  have hN := frameInputs_covariance_lower (by norm_num : 11883 ≤ 12225) F
  have htheta := F.window.1
  have hbeta := frameInputs_beta_nonneg F
  have hnum : F.N + F.xiF ≤ BstLean.Part249.optionBAgentFrame * F.d := by
    apply (div_le_iff₀ F.cutoff_pos).mp
    linarith [F.frame_scalar]
  have hcap := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ BstLean.Part249.optionBAgentFrame by norm_num [BstLean.Part249.optionBAgentFrame])
  norm_num [BstLean.Part249.optionBAgentFrame, BstLean.Part249.storedFrameCutoff] at hcap hnum
  linarith

/-- A necessary centre allowance for any successful certificate at the stored
cutoff. The bound concerns the allowance field, not the actual centre error. -/
theorem centre_allowance_necessary {c : Ret 12225}
    (F : BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame)
    (hd : F.d ≤ BstLean.Part249.storedFrameCutoff) : F.xiF < (8454 / 100000 : ℝ) := by
  by_contra h
  exact no_frameInputs_at_stored_cutoff F hd (le_of_not_gt h)

end BstLean.Part251
