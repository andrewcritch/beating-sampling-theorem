import BstLean.Part243Agent
import BstLean.Part196Junction
import BstLean.Part227Package

/-! Part 243: scalar certificates imply the original fixed-radius network conclusion.
The new Agent package has no unused legacy statistics fields. -/
namespace BstLean.Part243
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part160 BstLean.Part192
open BstLean.Part196 BstLean.Part169

theorem checked_failure {n : ℕ} (hn : 1 ≤ n) {w : WorldParameters}
    (W : WorldPackage (paperProgram n) w) {a : AgentParameters}
    (t : ℝ) (C : MasterCertificate n w a)
    (A : AgentPackage n (BstLean.Part159.Hof W.hidden) C.worldRadius a.frame a.root a.charge t)
    (hCharge : a.charge ≤ C.retainedCharge) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      (failNet (paperDesignP n) t aL (10 ^ 12)) ≤ C.totalBudget := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hEv := world_events W A.measurable A.retained_charge
  have hFW : FRAME_W_hyp (paperCentres n) (w.frame / n)
      (goodSet (BstLean.Part159.Hof W.hidden) A.event (HbarW (paperDesignP n))
        C.worldRadius) := fun c hc => W.frame_bound c hc.1.1
  have hEp : Eplus aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame
      C.positiveTilt ≤ 0 := C.positive_enclosure.trans (by linarith [C.positiveExponent_nonneg])
  have hEm : Eminus aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame
      C.negativeTilt ≤ 0 := C.negative_enclosure.trans (by linarith [C.negativeExponent_nonneg])
  have h := network_master hn (paperDesignP n) t (10 ^ 12)
    C.worldFrame_pos C.agentFrame_pos C.worldRadius_pos C.agentRoot_nonneg C.sampleRoot_pos
    (by norm_num [aL]) C.positiveTilt_pos C.negativeTilt_neg C.lower_radius C.lower_root
    hEp hEm hEv hFW A.frame_bound A.root_bound
  have hp : Bplus n aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame
      C.positiveTilt ≤ C.upperTail := by
    apply le_trans (exp_le_exp.mpr _) C.positive_tail
    have := mul_le_mul_of_nonneg_left C.positive_enclosure hnR.le
    linarith
  have hm : Bminus n aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame
      C.negativeTilt ≤ C.lowerTail := by
    apply le_trans (exp_le_exp.mpr _) C.negative_tail
    have := mul_le_mul_of_nonneg_left C.negative_enclosure hnR.le
    linarith
  calc
    _ ≤ w.hiddenCharge + w.moment / C.worldRadius ^ 2 + a.charge +
        Bplus n aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame C.positiveTilt +
        Bminus n aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame C.negativeTilt +
        2 * exp (-((10 ^ 12 : ℕ) : ℝ) * C.sampleRoot ^ 2) := h
    _ ≤ w.hiddenCharge + w.moment / C.worldRadius ^ 2 + C.retainedCharge +
        C.upperTail + C.lowerTail + C.samplingCharge :=
      add_le_add (add_le_add (add_le_add (add_le_add le_rfl hCharge) hp) hm) C.actual_sampling
    _ = w.hiddenCharge + w.moment / C.worldRadius ^ 2 + C.retainedCharge +
        C.samplingCharge + C.upperTail + C.lowerTail := by ring
    _ ≤ C.totalBudget := C.ledger

theorem checked_junction {n : ℕ} (hn : 1 ≤ n) {w : WorldParameters}
    (W : WorldPackage (paperProgram n) w) {a : AgentParameters}
    (t : ℝ) (C : MasterCertificate n w a)
    (A : AgentPackage n (BstLean.Part159.Hof W.hidden) C.worldRadius a.frame a.root a.charge t)
    (hCharge : a.charge ≤ C.retainedCharge) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  have h := (checked_failure hn W t C A hCharge).trans C.budget
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have he : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} =
      (failNet (paperDesignP n) t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  rw [he, measureReal_compl (measurableSet_failNet (paperDesignP n) t aL _), probReal_univ]
  norm_num
  linarith

/-- This bridge exposes the S14 TI premises and the retained frame/root supplies.
Part 238 can discharge the TI premises after its statements match these cells. -/
theorem scalar_to_network {n : ℕ} (hn : 8000 ≤ n) {w : WorldParameters}
    (W : WorldPackage (paperProgram n) w) {a : AgentParameters}
    (t : ℝ) (C : MasterCertificate n w a) {E : Set (Ret n)}
    (hE : MeasurableSet E) {charge thetaLo thetaHi lam₀ lam₁ : ℝ}
    {wideLo wideHi coreLo coreHi : ℝ}
    (hcharge : (retDist (paperCentres n)).real (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ charge)
    (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁) (hlam : lam₁ ≤ lam₀)
    (hwide_order : wideLo ≤ wideHi) (hcore_order : coreLo ≤ coreHi)
    (hwide_guard : ∀ θ ∈ Icc thetaLo thetaHi,
      BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide wideLo wideHi)
    (hcore_guard : ∀ θ ∈ Icc thetaLo thetaHi,
      BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore coreLo coreHi)
    (hwide : ∀ j < 12, BstLean.Part182.TI_hyp n
      (BstLean.Part235.overlapLo wideLo wideHi j)
      (BstLean.Part235.overlapHi wideLo wideHi j) lam₀ (50 * exp (-46)))
    (hcore : ∀ j < 12, BstLean.Part182.TI_hyp n
      (BstLean.Part235.overlapLo coreLo coreHi j)
      (BstLean.Part235.overlapHi coreLo coreHi j) lam₁ (50 * exp (-46)))
    (hframe : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceEvent n thetaLo thetaHi lam₀ lam₁) (HbarW (paperDesignP n)) C.worldRadius,
      Nonempty (FrameInputs n c thetaLo thetaHi lam₀ lam₁ a.frame))
    (hroot : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceEvent n thetaLo thetaHi lam₀ lam₁) (HbarW (paperDesignP n)) C.worldRadius,
      Nonempty (RootInputs n t c a.root))
    (hpayment : charge + 1 / 4000 ≤ a.charge)
    (hCharge : a.charge ≤ C.retainedCharge) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  have hτ : TauWorld (paperDesignP n) := paperDesign_tauWorld _ _ _ _
  let A := agentPackage hn hE hcharge hτ hl₀ hl₁ hlam hwide_order hcore_order
    hwide_guard hcore_guard hwide hcore hframe hroot
  have A' : AgentPackage n (BstLean.Part159.Hof W.hidden) C.worldRadius
      a.frame a.root a.charge t :=
    { A with retained_charge := A.retained_charge.trans hpayment }
  exact checked_junction (by omega) W t C A' hCharge

end BstLean.Part243
#print axioms BstLean.Part243.checked_failure
#print axioms BstLean.Part243.checked_junction
#print axioms BstLean.Part243.scalar_to_network
