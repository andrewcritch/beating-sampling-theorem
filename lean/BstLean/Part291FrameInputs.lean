import BstLean.Part291ProjectedJacobian
import BstLean.Part291ResidualMoments
import BstLean.Part291GBFormula
import BstLean.Part291WeightedDensity

/-! Assemble every weighted Poincare and moment premise for the actual network.
The remaining frame input is the weighted Schur quadratic form. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182 BstLean.Part188 BstLean.Part222

noncomputable def frameGB (n : ℕ) (a d M H Ncov xiF : ℝ) : ℝ :=
  ((Ncov + xiF) / d) ^ (41 / 45 : ℝ) * ((n : ℝ) / d) ^ (4 / 45 : ℝ) *
    (1 + H) ^ (8 / 45 : ℝ) * ((a - d) / d ^ 2) * (M / n)

theorem weightedTests_from_interfaces {n : ℕ} (hn : 50 ≤ n) (D : Design n) (c : Ret n)
    {u d M H xiP E Ncov xiF Npsi : ℝ}
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j)
    (hI : WFInterfaces D c M H xiP) (hE : centreEnergy D c ≤ E)
    (hcov : COV_at D c Ncov) (hcen : CENTRE_at D c xiF)
    (hNc : 0 ≤ Ncov) (hxi : 0 ≤ xiF) (hN : 0 ≤ Npsi)
    (hu : 0 < u) (hu1 : u < 1) (hd : 0 < d)
    (hY : d < (1 - u) ^ 2 - (√E + √(xiP / n)) ^ 2)
    (hSchur : ∀ w : Fin (mA n) → ℝ,
      (∫ ξ, (wN c.1.2 (D.tau0 c) ξ * weightSq ((1 - u) ^ 2) d (centreCoordinate D c ξ)) *
        normSq (vecMul w (BJ c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ξ)) ∂stdGauss (Fin n)) ≤
          Npsi * normSq w)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1) :
    WeightedTestBounds D c v ((1 - u) ^ 2) d Npsi
      (frameGB n ((1 - u) ^ 2) d M H Ncov xiF) xiF Ncov
      (((1 - u) ^ 2 - d) / d ^ 3 * (M / n))
      (√(rwWeightMean ((1 - u) ^ 2) d (√E + √(xiP / n)) (√(M / n))))
      (massBound n M H xiP E u d) := by
  have hp : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hm0 : 0 ≤ √E + √(xiP / n) := by positivity
  have hmean0 : 0 ≤ ∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n) :=
    integral_nonneg (centreCoordinate_nonneg D c hb0)
  have hmean : (∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n)) ≤ √E + √(xiP / n) := by
    have hp := (abs_le.mp hI.parallel.2).2
    have hs := sqrt_le_sqrt hE
    linarith
  have hd' : d < (1 - u) ^ 2 := by nlinarith [sq_nonneg (√E + √(xiP / n))]
  have hgap : 0 < √((1 - u) ^ 2 - d) - (√E + √(xiP / n)) := by
    have h := (lt_sqrt hm0).mpr (by linarith : (√E + √(xiP / n)) ^ 2 < (1 - u) ^ 2 - d)
    linarith
  have hRW := rw_deficit_network hn D c hτ hb hI.direction hmean0 hmean
  refine ⟨projectedEnergy_from_schur (by omega) D c hτ hd hN hSchur v hv,
    gb_network_cap_normalized (by omega) D c v hv hd hd'.le (add_nonneg hNc hxi)
      hI.direction hI.energy (residual_second_from_sources (by omega) D c hNc hcov hcen v hv),
    weight_mean_from_RW (stdGauss (Fin n)) (centreCoordinate D c) (measurable_centreCoordinate D c)
      hd hY hm0 (sqrt_nonneg _) hRW,
    weight_variance_network (by omega) D c hτ hd hd'.le hI.direction,
    residualTest_variance_bound (by omega) D c hNc hcov v hv,
    residualTest_mean_bound (by omega) D c hcen v hv,
    sharp_good_mass hn D c hτ hb hb0 hI hE hu hu1 hd' hgap⟩

end BstLean.BlueprintLow
