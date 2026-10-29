import BstLean.Part259Local

/-! The local frame enters the existing dimension-n classifier junction. -/
namespace BstLean.Part259
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part199 BstLean.Part161 BstLean.Part182
open BstLean.Part169 (paperDesignP)
open BstLean.Part192 BstLean.Part196 BstLean.Part156

open BstLean.Part249

/-- The moment event and covariance event cost .0003 in total.
The base event excludes those two payments. -/
noncomputable def agentPackage {n : ℕ} (hn : 11883 ≤ n) {event : Set (AgFam n)} {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ}
    {H E : Set (Ret n)} (hevent : MeasurableSet event)
    (hpayment : (retDist (paperCentres n)).real
      (agentEv (paperDesignP n) event)ᶜ ≤ (1/4000 : ℝ))
    (hE : MeasurableSet E)
    {radius frame root charge t : ℝ}
    (hcharge : (retDist (paperCentres n)).real (H ∩ Eᶜ) ≤ charge)
    (hframe : ∀ c ∈ goodSet H (E ∩ covarianceGood event)
      (HbarW (paperDesignP n)) radius, Nonempty (LocalFrameInputs n event cell capTable c frame))
    (hroot : ∀ c ∈ goodSet H (E ∩ covarianceGood event)
      (HbarW (paperDesignP n)) radius, Nonempty (BstLean.Part243.RootInputs n t c root)) :
    BstLean.Part243.AgentPackage n H radius frame root (charge + 3 / 10000) t := by
  have hTI := covarianceGood_charge hn hpayment
  refine { event := E ∩ covarianceGood event
           measurable := hE.inter (covarianceGood_measurable hevent)
           retained_charge := ?_
           frame_bound := ?_
           root_bound := ?_ }
  · have hs : H ∩ (E ∩ covarianceGood event)ᶜ ⊆
        (H ∩ Eᶜ) ∪ (covarianceGood event)ᶜ := by
      intro c hc
      by_cases he : c ∈ E
      · exact Or.inr (fun ht => hc.2 ⟨he, ht⟩)
      · exact Or.inl ⟨hc.1, he⟩
    exact (measureReal_mono hs (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add hcharge hTI))
  · intro c hc v
    obtain ⟨F⟩ := hframe c hc
    exact frame_from_inputs (by omega) F hc.2.2 v
  · intro c hc
    obtain ⟨R⟩ := hroot c hc
    exact (BstLean.Part241.root_new_8000 (by omega) t c R.split R.window R.passes
      R.fluctuation).trans R.scalar

/-- Per-dimension packages supply the classifier. Scalar data alone do not supply
the World event, local covariance contract, or stored-pass root. -/
theorem classifier_from_inputs {n : ℕ} (hn : 11883 ≤ n)
    {event : Set (AgFam n)} {cell : Fin 60 → Set ℝ} {caps : Fin 60 → ℝ}
    {w : WorldParameters} {a : AgentParameters}
    (W : WorldPackage (paperProgram n) w) (C : MasterCertificate n w a)
    (t : ℝ) {E : Set (Ret n)} (hevent : MeasurableSet event)
    (hpayment : (retDist (paperCentres n)).real
      (agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ))
    (hE : MeasurableSet E) {charge : ℝ}
    (hcharge : (retDist (paperCentres n)).real
      (BstLean.Part159.Hof W.hidden ∩ Eᶜ) ≤ charge)
    (hframe : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceGood event) (HbarW (paperDesignP n)) C.worldRadius,
      Nonempty (LocalFrameInputs n event cell caps c a.frame))
    (hroot : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceGood event) (HbarW (paperDesignP n)) C.worldRadius,
      Nonempty (BstLean.Part243.RootInputs n t c a.root))
    (hpay : charge + 3 / 10000 ≤ a.charge)
    (hcompat : a.charge ≤ C.retainedCharge) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  have A := agentPackage hn hevent hpayment hE hcharge hframe hroot
  have A' : BstLean.Part243.AgentPackage n (BstLean.Part159.Hof W.hidden)
      C.worldRadius a.frame a.root a.charge t :=
    { A with retained_charge := A.retained_charge.trans hpay }
  exact BstLean.Part243.checked_junction (by omega) W t C A' hcompat

end BstLean.Part259
