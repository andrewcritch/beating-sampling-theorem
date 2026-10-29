import BstLean.Part278Chain
import BstLean.Part267Family

/-!
# Part 278 (O5, the 12 225 family): the stated program, conditional on the odd root

* `classifier_from_inputs_st`: copy of `Part259.classifier_from_inputs` for `statedDesign n`,
  with the extra premise `hodd` on the good set.
* `OddRoot R t`: the odd-root premise for one row of `Part259.RowInputs`.
* `classifier_from_row_st`, `classifier_on_set_st`.
* `classifier_stated_12225_12349_of_odd`: the theorem `Part267.classifier_12225_12349` for
  `progOut (statedDesign n)`. For even `n` it holds with no premise
  (`Part272.statedDesign_even`); for odd `n` it takes the premise `OddRoot` of the family row.
-/

namespace BstLean.Part278

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part160 BstLean.Part192
open BstLean.Part196 BstLean.Part169 BstLean.Part259
open BstLean.Part272 (statedDesign)

theorem classifier_from_inputs_st {n : ℕ} (hn : 11883 ≤ n)
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
    (hodd : ∀ c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (E ∩ covarianceGood event) (HbarW (paperDesignP n)) C.worldRadius,
      |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20)
    (hpay : charge + 3 / 10000 ≤ a.charge)
    (hcompat : a.charge ≤ C.retainedCharge) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (statedDesign n) t aL (10 ^ 12) x.1 x.2)} := by
  let A := agentPackage hn hevent hpayment hE hcharge hframe hroot
  let A' : BstLean.Part243.AgentPackage n (BstLean.Part159.Hof W.hidden)
      C.worldRadius a.frame a.root a.charge t :=
    { A with retained_charge := A.retained_charge.trans hpay }
  have hRst : REPLA_mix_hyp (statedDesign n) t a.root
      (goodSet (BstLean.Part159.Hof W.hidden) (E ∩ covarianceGood event)
        (HbarW (paperDesignP n)) C.worldRadius) := by
    intro c hc
    obtain ⟨R⟩ := hroot c hc
    exact rootInputs_st (by omega) R (hodd c hc)
  exact checked_junction_st (by omega) W t C A' hRst hcompat

/-- The odd-root premise for one row. -/
def OddRoot {n : ℕ} (R : RowInputs n) (t : ℝ) : Prop :=
  ∀ c ∈ goodSet (BstLean.Part159.Hof R.world.hidden)
    (R.baseEvent ∩ covarianceGood R.covarianceEvent) (HbarW (paperDesignP n))
    R.certificate.worldRadius,
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20

theorem classifier_from_row_st {n : ℕ} (R : RowInputs n) (t : ℝ) (hodd : OddRoot R t) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (statedDesign n) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_from_inputs_st R.dimension R.world R.certificate t
    R.covariance_measurable R.covariance_payment R.base_measurable
    R.base_payment R.frame (R.root t) hodd R.payment R.charge_compatible

theorem classifier_on_set_st {S : Set ℕ} (R : FamilyInputs S)
    (hodd : ∀ n (hn : n ∈ S), Odd n → ∀ t, OddRoot (R.row n hn) t) :
    ∀ n ∈ S, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (statedDesign n) t aL (10 ^ 12) x.1 x.2)} := by
  intro n hn t
  rcases Nat.even_or_odd n with he | ho
  · rw [BstLean.Part272.statedDesign_even (by have := (R.row n hn).dimension; omega) he]
    exact classifier_from_row (R.row n hn) t
  · exact classifier_from_row_st (R.row n hn) t (hodd n hn ho t)

/-- **The 12 225 family for the stated program.** Even `n`: no premise. Odd `n`: the odd-root
premise of the family row. -/
theorem classifier_stated_12225_12349_of_odd
    (hodd : ∀ n (hn : n ∈ Set.Icc (12225 : ℕ) 12349), Odd n → ∀ t,
      OddRoot (BstLean.Part267.familyInputs.row n hn) t) :
    ∀ n ∈ Set.Icc (12225 : ℕ) 12349, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (statedDesign n) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_on_set_st BstLean.Part267.familyInputs hodd

end BstLean.Part278
