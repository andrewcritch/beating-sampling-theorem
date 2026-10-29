import BstLean.Part259Bridge
import BstLean.Part243Interval

/-! Dimension-dependent local supplies give coverage on an arbitrary dimension set.
The structure keeps analytic supplies distinct from rational scalar checks. -/
namespace BstLean.Part259
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part160 (AgFam agentEv)
open BstLean.Part169 (paperDesignP)

structure RowInputs (n : ℕ) where
  dimension : 11883 ≤ n
  worldParameters : WorldParameters
  agentParameters : AgentParameters
  world : WorldPackage (paperProgram n) worldParameters
  certificate : MasterCertificate n worldParameters agentParameters
  covarianceEvent : Set (AgFam n)
  cell : Fin 60 → Set ℝ
  caps : Fin 60 → ℝ
  covariance_measurable : MeasurableSet covarianceEvent
  covariance_payment : (retDist (paperCentres n)).real
    (agentEv (paperDesignP n) covarianceEvent)ᶜ ≤ (1 / 4000 : ℝ)
  baseEvent : Set (Ret n)
  base_measurable : MeasurableSet baseEvent
  baseCharge : ℝ
  base_payment : (retDist (paperCentres n)).real
    (BstLean.Part159.Hof world.hidden ∩ baseEventᶜ) ≤ baseCharge
  frame : ∀ c ∈ goodSet (BstLean.Part159.Hof world.hidden)
    (baseEvent ∩ covarianceGood covarianceEvent) (HbarW (paperDesignP n))
    certificate.worldRadius,
    Nonempty (LocalFrameInputs n covarianceEvent cell caps c agentParameters.frame)
  root : ∀ (t : ℝ) c, c ∈ goodSet (BstLean.Part159.Hof world.hidden)
    (baseEvent ∩ covarianceGood covarianceEvent) (HbarW (paperDesignP n))
    certificate.worldRadius →
    Nonempty (BstLean.Part243.RootInputs n t c agentParameters.root)
  payment : baseCharge + 3 / 10000 ≤ agentParameters.charge
  charge_compatible : agentParameters.charge ≤ certificate.retainedCharge

theorem classifier_from_row {n : ℕ} (R : RowInputs n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_from_inputs R.dimension R.world R.certificate t
    R.covariance_measurable R.covariance_payment R.base_measurable
    R.base_payment R.frame (R.root t) R.payment R.charge_compatible

structure FamilyInputs (S : Set ℕ) where
  row : ∀ n ∈ S, RowInputs n

theorem classifier_on_set {S : Set ℕ} (R : FamilyInputs S) :
    ∀ n ∈ S, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  intro n hn t
  exact classifier_from_row (R.row n hn) t

end BstLean.Part259
