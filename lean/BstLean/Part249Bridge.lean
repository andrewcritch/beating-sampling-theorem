import BstLean.Part249Covariance
import BstLean.Part249Row

/-! A conditional network junction with the actual Option B covariance event.
The local frame, root, base-event payment and World supplies remain explicit. -/
namespace BstLean.Part249
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part199 BstLean.Part161 BstLean.Part182
open BstLean.Part169 (paperDesignP)
open BstLean.Part192 BstLean.Part196 BstLean.Part156

structure FrameInputs (n : ℕ) (c : Ret n) (cf : ℝ) where
  M : ℝ
  H : ℝ
  xiP : ℝ
  E : ℝ
  u : ℝ
  d : ℝ
  N : ℝ
  xiF : ℝ
  beta : ℝ
  scale_pos : 0 < (paperDesignP n).tau0 c
  window : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
    Icc (46 / 100) (528 / 1000)
  centre_pos : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1)
  centre_nonneg : ∀ j, 0 ≤ (paperDesignP n).bA c.1 c.2.1.1 j
  interfaces : WFInterfaces (paperDesignP n) c M H xiP
  centre_energy : centreEnergy (paperDesignP n) c ≤ E
  u_pos : 0 < u
  u_lt : u < 1
  cutoff_pos : 0 < d
  cutoff_lt : d < (1-u)^2
  gap_pos : 0 < √((1-u)^2-d) - (√E + √(xiP/n))
  covariance_nonneg : 0 ≤ N
  covariance_scalar : BstLean.Part238.sharpScalar n
    (BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c)) exampleWide exampleCore
    (min (BstLean.Part238.sharpK (595 / 1000) (35 / 1000) (25 / 100) (51 / 100))
      (BstLean.Part182.ta_lam (595 / 1000) (35 / 1000) (25 / 100)))
    (67 / 100)
    (1 - 4 * BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) / n)⁻¹
    (13 / 10) (2 * exp (-exampleWide.pair ^ 2 / 2) +
      2 * (optionBDelta n / (1 / 4000))) ≤ N
  full_centre : CENTRE_at (paperDesignP n) c xiF
  mass_scalar : BstLean.Part222.massBound n M H xiP E u d ≤ beta
  frame_scalar : (N + xiF) / d + beta ≤ cf

theorem frame_from_inputs {n : ℕ} (hn : 11883 ≤ n) {c : Ret n} {cf : ℝ}
    (F : FrameInputs n c cf) (hc : c ∈ optionBGood (paperDesignP n)) :
    ∀ v : Fin (mA n) → ℝ,
      ∫ ξ, (∑ j, BstLean.Part134.eDir ((paperDesignP n).bA c.1 c.2.1.1)
        (hStand (paperDesignP n) c ξ) j * v j)^2 ∂BstLean.Part29.stdGauss (Fin n) ≤
      cf / n * ∑ j, v j^2 := by
  have hcov := BstLean.Part238.cov_at_sharp_M12 hn (paperDesignP n) c F.scale_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    F.window (hc.2 F.scale_pos) (hc.1 F.scale_pos) F.covariance_scalar
  exact BstLean.Part222.freeAllowance_frame (by omega) (paperDesignP n) c
    F.scale_pos F.centre_pos F.centre_nonneg F.interfaces F.centre_energy
    F.u_pos F.u_lt F.cutoff_pos F.cutoff_lt F.gap_pos F.covariance_nonneg hcov
    F.full_centre F.mass_scalar F.frame_scalar

/-- The moment event and covariance event cost .0003 in total.
The base event excludes those two payments. -/
noncomputable def agentPackage {n : ℕ} (hn : 11883 ≤ n)
    {H E : Set (Ret n)} (hE : MeasurableSet E)
    {radius frame root charge t : ℝ}
    (hcharge : (retDist (paperCentres n)).real (H ∩ Eᶜ) ≤ charge)
    (hframe : ∀ c ∈ goodSet H (E ∩ optionBGood (paperDesignP n))
      (HbarW (paperDesignP n)) radius, Nonempty (FrameInputs n c frame))
    (hroot : ∀ c ∈ goodSet H (E ∩ optionBGood (paperDesignP n))
      (HbarW (paperDesignP n)) radius, Nonempty (BstLean.Part243.RootInputs n t c root)) :
    BstLean.Part243.AgentPackage n H radius frame root (charge + 3 / 10000) t := by
  have hTI := optionB_good_charge hn (paperDesignP n) (paperDesign_tauWorld _ _ _ _)
  refine { event := E ∩ optionBGood (paperDesignP n)
           measurable := hE.inter (optionBGood_measurable _)
           retained_charge := ?_
           frame_bound := ?_
           root_bound := ?_ }
  · have hs : H ∩ (E ∩ optionBGood (paperDesignP n))ᶜ ⊆
        (H ∩ Eᶜ) ∪ (optionBGood (paperDesignP n))ᶜ := by
      intro c hc
      by_cases he : c ∈ E
      · exact Or.inr (fun ht => hc.2 ⟨he, ht⟩)
      · exact Or.inl ⟨hc.1, he⟩
    exact (measureReal_mono hs (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add hcharge hTI))
  · intro c hc v
    obtain ⟨F⟩ := hframe c hc
    exact frame_from_inputs hn F hc.2.2 v
  · intro c hc
    obtain ⟨R⟩ := hroot c hc
    exact (BstLean.Part241.root_new_8000 (by omega) t c R.split R.window R.passes
      R.fluctuation).trans R.scalar

/-- The revised row has no TI or fourth-moment hypothesis. It still requires the
actual World package and the remaining charged local frame/root inputs. -/
theorem row_classifier_from_inputs
    (W : WorldPackage (paperProgram 12225)
      (BstLean.Part243.rowWorldParameters BstLean.Part243.proposedHiddenCharge))
    (t : ℝ) {E : Set (Ret 12225)} (hE : MeasurableSet E)
    (hcharge : (retDist (paperCentres 12225)).real
      (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ baseChargeAllowance)
    (hframe : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ optionBGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius, Nonempty (FrameInputs 12225 c optionBAgentFrame))
    (hroot : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ optionBGood (paperDesignP 12225)) (HbarW (paperDesignP 12225))
      BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot)) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} := by
  have A := agentPackage (by norm_num : 11883 ≤ 12225) hE hcharge hframe hroot
  rw [base_charge_restored] at A
  exact BstLean.Part243.checked_junction (by norm_num) W t optionBScalarRow A le_rfl

end BstLean.Part249
