import BstLean.Part196Master

/-! Part 196: checked scalar certificates supply the network master guards. -/
namespace BstLean.Part196
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192

/-- The two endpoint radius guards and the actual sampling payment are explicit.
The inherited payment at exponent 100 alone does not bound an arbitrary tolerance. -/
structure MasterCertificate (n : ℕ) (w : WorldParameters) (a : AgentParameters)
    extends EndpointCertificate n w a where
  lower_radius : a.root + sampleRoot + worldRadius < √(1 / 100 / aL)
  lower_root : 2 * (a.root + sampleRoot) ≤ √(1 / 100 / aL)
  actual_sampling : 2 * exp (-((10 ^ 12 : ℕ) : ℝ) * sampleRoot ^ 2) ≤ samplingCharge

theorem checked_failure {n : ℕ} (hn : 1 ≤ n) (P : Program n)
    {w : WorldParameters} (W : WorldPackage P w) {a : AgentParameters}
    {m : MomentParameters} (t : ℝ) (C : MasterCertificate n w a)
    (A : AgentJunctionPackage P W a m C.worldRadius t)
    (hCharge : a.charge ≤ C.retainedCharge) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      (failNet P.design t aL (10 ^ 12)) ≤ C.totalBudget := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hEv := world_events W A.event_measurable A.retained_charge
  have hFW : FRAME_W_hyp P.design.toCentres (w.frame / n)
      (goodSet (BstLean.Part159.Hof W.hidden) A.event (HbarW P.design)
        C.worldRadius) := fun c hc => W.frame_bound c hc.1.1
  have hEp : Eplus aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame
      C.positiveTilt ≤ 0 := C.positive_enclosure.trans (by linarith [C.positiveExponent_nonneg])
  have hEm : Eminus aL (a.root + C.sampleRoot) C.worldRadius w.frame a.frame
      C.negativeTilt ≤ 0 := C.negative_enclosure.trans (by linarith [C.negativeExponent_nonneg])
  have h := network_master hn P.design t (10 ^ 12) C.worldFrame_pos C.agentFrame_pos
    C.worldRadius_pos C.agentRoot_nonneg C.sampleRoot_pos (by norm_num [aL])
    C.positiveTilt_pos C.negativeTilt_neg C.lower_radius C.lower_root hEp hEm
    hEv hFW A.frame A.root
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
      add_le_add (add_le_add (add_le_add (add_le_add le_rfl hCharge) hp) hm)
        C.actual_sampling
    _ = w.hiddenCharge + w.moment / C.worldRadius ^ 2 + C.retainedCharge +
        C.samplingCharge + C.upperTail + C.lowerTail := by ring
    _ ≤ C.totalBudget := C.ledger

/-- The exact-moment program succeeds for each fixed threshold on compatible packages. -/
theorem checked_junction {n : ℕ} (hn : 1 ≤ n) (P : Program n)
    {w : WorldParameters} (W : WorldPackage P w) {a : AgentParameters}
    {m : MomentParameters} (t : ℝ) (C : MasterCertificate n w a)
    (A : AgentJunctionPackage P W a m C.worldRadius t)
    (hCharge : a.charge ≤ C.retainedCharge) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut P.design t aL (10 ^ 12) x.1 x.2)} := by
  have h := (checked_failure hn P W t C A hCharge).trans C.budget
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have he : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut P.design t aL (10 ^ 12) x.1 x.2)} =
      (failNet P.design t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  rw [he, measureReal_compl (measurableSet_failNet P.design t aL _), probReal_univ]
  norm_num
  linarith

end BstLean.Part196
