import BstLean.Part264Supply12226
import BstLean.Part264PilotRepair
import BstLean.Part264Covariance

/-! Actual selected covariance at 12226, with the original single payment. -/
namespace BstLean.Part264
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters)
open BstLean.Part263 (scalarRow12226)

noncomputable def covarianceInputs12226 :
    BstLean.Part263.CovarianceInputs 12226 scalarRow12226.grid parameters (caps repair12226) :=
  covarianceInputs_from_supplies (by norm_num) repair12226 supplies12226
    (fun j _ hθ => radii12226 j hθ)

noncomputable def covarianceEvent12226 : Set (AgFam 12226) :=
  BstLean.Part263.covarianceEvent 12226 scalarRow12226.grid parameters

theorem covarianceEvent12226_measurable : MeasurableSet covarianceEvent12226 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent12226_payment :
    (retDist (paperDesignP 12226).toCentres).real
      (agentEv (paperDesignP 12226) covarianceEvent12226)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs12226

theorem localCov12226 : BstLean.Part259.LocalCovarianceOn covarianceEvent12226
    (BstLean.Part263.cell scalarRow12226.grid) (caps repair12226) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs12226

theorem covarianceGood12226_payment :
    (retDist (paperDesignP 12226).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent12226)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent12226_payment

end BstLean.Part264
