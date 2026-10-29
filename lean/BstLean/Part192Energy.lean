import BstLean.Part192Agent

/-! Part 192: the legacy energy supplies with explicit orders and distributions.
The order-eight residual scale and the order-four/order-24 kept location means
are different supplies from the sharp order-32 inputEnergy interface. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part161 (muI)

structure EnergySupply (n : ℕ) (charge scaleBound locationBound : ℝ) where
  event : Set (Ret n)
  event_measurable : MeasurableSet event
  event_charge : (retDist (paperCentres n)).real eventᶜ ≤ charge
  scale8 : ∀ c ∈ event, 0 < (paperDesignP n).tau0 c →
    ∫ a, ∫ v, BstLean.Part162.sgA (paperDesignP n) c a v ^ 8
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤ scaleBound ^ 8
  location4 : ∀ c ∈ event, 0 < (paperDesignP n).tau0 c →
    ∫ a in BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.KR c,
      fbR c a ^ 4 ∂muI n ≤ locationBound ^ 4
  location24 : ∀ c ∈ event, 0 < (paperDesignP n).tau0 c →
    ∫ a in BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.KR c,
      fbR c a ^ 24 ∂muI n ≤ locationBound ^ 24

noncomputable def energy16200 {n : ℕ} (hn : 16200 ≤ n) :
    EnergySupply n (1 / 10 ^ 6) (1005 / 1000 * √(2 / (n : ℝ))) (1005 / 1000) where
  event := agentEv (paperDesignP n) (BstLean.Part177.SEn n)
  event_measurable := measurableSet_agentEv _ (BstLean.Part177.measurableSet_SEn n)
  event_charge := energy_event16200 hn
  scale8 := fun _ hc hτ => BstLean.Part177.sg8_of_SEn (by omega) _ hc hτ
  location4 := fun _ hc hτ =>
    (BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).2
  location24 := fun _ hc hτ =>
    (BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.fb_of_SEn (by omega) hc hτ).1

end BstLean.Part192
#print axioms BstLean.Part192.energy16200
