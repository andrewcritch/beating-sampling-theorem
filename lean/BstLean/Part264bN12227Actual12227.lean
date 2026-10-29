import BstLean.Part264bN12227Supply12227
import BstLean.Part264Coverage
import BstLean.Part264Covariance

/-! Actual selected covariance at 12227, with the original single payment. -/
namespace BstLean.Part264b.N12227
open BstLean.Part264
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters)
open BstLean.Part263 (scalarRow12227)

noncomputable def covarianceInputs12227 :
    BstLean.Part263.CovarianceInputs 12227 scalarRow12227.grid parameters (caps repair12227) :=
  covarianceInputs_from_supplies (by norm_num) repair12227 supplies12227
    (fun j _ hθ => radii12227 j hθ)

noncomputable def covarianceEvent12227 : Set (AgFam 12227) :=
  BstLean.Part263.covarianceEvent 12227 scalarRow12227.grid parameters

theorem covarianceEvent12227_measurable : MeasurableSet covarianceEvent12227 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12227_payment :
    (retDist (paperDesignP 12227).toCentres).real
      (agentEv (paperDesignP 12227) covarianceEvent12227)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12227

theorem localCov12227 : BstLean.Part259.LocalCovarianceOn covarianceEvent12227
    (BstLean.Part263.cell scalarRow12227.grid) (caps repair12227) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12227

theorem covarianceGood12227_payment :
    (retDist (paperDesignP 12227).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12227)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12227_payment

end BstLean.Part264b.N12227
