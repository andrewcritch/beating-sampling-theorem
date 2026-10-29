import BstLean.Part269Repair13224
import BstLean.Part269BlockSupplies2
namespace BstLean.Part269.N13224
open Real Set MeasureTheory BstLean.Part264 BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters sourceIndex)
open BstLean.Part263 (cell cellLower cellUpper Supply)
theorem grid_top_bounds13224 : scalarRow13224.grid.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000) := by
  constructor <;> norm_num [scalarRow13224, grid13224, endpointGrid13224]

theorem supplies13224 (j : Fin 43) : Supply 13224 (parameters j)
    (cellLower scalarRow13224.grid (sourceIndex j))
    (cellUpper scalarRow13224.grid (sourceIndex j)) := BstLean.Part269.BG2.supplies (n := 13224) (by constructor <;> norm_num) scalarRow13224.grid grid_top_bounds13224 j

noncomputable def covarianceInputs13224 : BstLean.Part263.CovarianceInputs 13224 scalarRow13224.grid parameters (caps repair13224) :=
  BstLean.Part269.BG2.covarianceInputs (by constructor <;> norm_num) scalarRow13224 grid_top_bounds13224 repair13224

noncomputable def covarianceEvent13224 : Set (AgFam 13224) :=
  BstLean.Part263.covarianceEvent 13224 scalarRow13224.grid parameters

theorem covarianceEvent13224_measurable : MeasurableSet covarianceEvent13224 :=
  BstLean.Part263.covarianceEvent_measurable _ _ _

theorem covarianceEvent13224_payment :
    (retDist (paperDesignP 13224).toCentres).real
      (agentEv (paperDesignP 13224) covarianceEvent13224)ᶜ ≤ (1 / 4000 : ℝ) :=
  BstLean.Part263.covarianceEvent_payment (by norm_num) covarianceInputs13224

theorem localCov13224 : BstLean.Part259.LocalCovarianceOn covarianceEvent13224
    (BstLean.Part263.cell scalarRow13224.grid) (caps repair13224) :=
  BstLean.Part263.localCov (by norm_num) covarianceInputs13224

theorem covarianceGood13224_payment :
    (retDist (paperDesignP 13224).toCentres).real
      (BstLean.Part259.covarianceGood covarianceEvent13224)ᶜ ≤ (3 / 10000 : ℝ) :=
  BstLean.Part259.covarianceGood_charge (by norm_num) covarianceEvent13224_payment



end BstLean.Part269.N13224
